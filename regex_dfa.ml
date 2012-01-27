open Batteries
open Printf

open Minreg

(* magic constants *)
let bits_per_char = 8
let num_chars = (1 lsl bits_per_char)
let max_commonality = num_chars

let map_of_val s v = IMap.set_to_map s v

type 'a norm_regex = int list * 'a Minreg.t IMap.t

(* takes norm_regex enum and returns a single norm_regex *)
let merge2 e1 e2 =
  if Minreg.compare e1 e2 = 0 then e1
  else reduce_union e1 e2

let merge_dlists d1 d2 = List.rev_append d1 d2 |> List.sort_unique Pervasives.compare
(* for constructing DFAs that use lists as decisions *)
let merging_dec_lists = ([],(fun i -> [i]), merge_dlists)
(*
let last_depth = Value.observe_int_ref "cur-depth canonized" (ref 0)
and last_width = Value.observe_int_ref "cur-width canonized" (ref 0)
*)
let reduce_pair merge_d (d1, m1) (d2,m2) =
  if IMap.is_empty m1 && IMap.is_empty m2 then
    (merge_d d1 d2), m1
  else
    (merge_d d1 d2), (IMap.union merge2 m1 m2)


let canonize (nul_d, inj_d, merge_d) rx =
  let merge norms = Enum.reduce (reduce_pair merge_d) norms in

  let canonized = ref (Map.create Minreg.compare) in

  let rec canon rx =
    let map_base = IMap.empty ~eq:Minreg.eq in
    try Map.find rx !canonized
    with Not_found ->
      (* insert a dummy value to prevent loops *)
      canonized := Map.add rx (nul_d, map_base) !canonized;
      let ret = match rx with
	| Concat (Value x::t, red) ->
	    nul_d, map_of_val x (Concat (t,red))
	| Union x when Set.is_empty x -> nul_d, map_base
	| Union x -> merge (Set.enum x |> map canon |> tap Enum.force)
	| Concat ((Kleene x) :: t, red) ->
	    let tl = Concat (t,red) in
	    canon (union2 tl (concat [x;Kleene x;tl]))
	| Value x -> nul_d, (map_of_val x epsilon)
	| Kleene x -> union2 epsilon (concat [x; Kleene x]) |> canon
	| Concat (Union u :: t, _) ->
	    union (Set.map (append t) u) |> canon
	| Accept i -> inj_d i, map_base
	| Concat (Concat _ :: _, _) -> assert false
	| Concat ([],_) -> assert false
	| Concat (Accept i::[],_) -> inj_d i, map_base
	| Concat (Accept _::_,_) -> assert false
      in
(*      eprintf "#Canonizing: %a\n%!" (Minreg.printp ~dec:false) rx;
      eprintf "#Result: %a\n%!" print_norm_regexp ret; *)
(*      last_depth := depth rx; last_width := width rx; *)
      canonized := Map.add rx ret !canonized;
      ret
  in
  reduce rx |> canon

(*
let c_time = Time.create "Canonize"
let canonize x = Time.start c_time; let r = canonize x in Time.stop c_time; r
*)

open Ean_std

type 'a fa = {
  qs: 'a array;
  q0: 'a;
}

type ('a,'b, 'c) state = {
  id    : int;
  label : 'a;
  map   : 'b;
  dec   : 'c;
}

type 'a dfa_state = ('a, int IMap.t, int list) state
type 'a dfa = 'a dfa_state fa

type qset = int Set.t
type 'a nfa_label = {n_label: 'a; mutable epsilon: qset}
type ('a,'b) nfa_state = ('a nfa_label, qset IMap.t, 'b) state
type ('a,'b) nfa = ('a,'b) nfa_state fa

let size {qs=qs} = Array.length qs
let trans {qs=qs} =
  let trans_q acc q =
    IMap.fold_range (fun lo hi _ (rngs,inds) -> rngs+1, inds+hi-lo+1) q.map acc
  in
  Array.fold_left trans_q (0,0) qs
let map_qs f fa = let qs = Array.map f fa.qs in {qs=qs; q0=qs.(fa.q0.id)}
let decs fa = Array.map (fun q -> q.dec) fa.qs
let get_map dfa i = dfa.qs.(i).map

let print_ids dfa = iter (fun i -> printf "%d) %d  " i dfa.qs.(i).id) (0 --^ size dfa)
let print_iset oc s = Set.print ~first:"{" ~sep:"," ~last:"}" Int.print oc s
let check_ids dfa = assert (for_all (fun i -> if dfa.qs.(i).id <> i then (eprintf "ID FAIL: id %d found at position %d" dfa.qs.(i).id i; print_ids dfa; assert false) else true ) (0 --^ size dfa)); dfa

let index_print print_v oc i v = fprintf oc "#%d) %a\n" i print_v v

let print_fa ?(ids=true) print_q oc {qs=qs; q0=_q0} =
  if ids then
    Array.iteri (index_print print_q oc) qs
  else
    Array.print ~first:"" ~last:"" ~sep:"" print_q oc qs;
  ()

let print_tmap oc v = IMap.iter_range (print_range Int.print oc) v
let print_ntmap oc v = IMap.iter_range (print_range (List.print Int.print) oc) v
let print_ntmap2 oc v = IMap.iter_range (print_range (Set.print ~first:"{" ~last:"}" ~sep:"," Int.print) oc) v

let print_dfa write_label write_dec oc dfa =
  let print_q oc {label=label;map=map;dec=dec} =
    fprintf oc "%a\n#%a %a\n" write_label label print_tmap map write_dec dec;
  in
  print_fa print_q oc dfa

let print_nfa write_label write_dec oc nfa =
  let print_q oc {id=id;label={n_label=nlabel; epsilon=eps};map=map;dec=dec} =
    if not (IMap.is_empty map && dec = []) then
      fprintf oc "#%d) %a %a %a %a\n" id
        write_label nlabel
        (fun oc e -> if Set.is_empty e then () else fprintf oc " eps: %a" print_iset e) eps
        print_ntmap2 map
        write_dec dec;
  in
  print_fa ~ids:false print_q oc nfa

let print_label oc (lo,hi) =
  if lo=0 && hi = num_chars - 1 then IO.write oc '*'
  else if lo = hi then fprintf oc "%C" (Char.chr lo)
  else fprintf oc "%C-%C" (Char.chr lo) (Char.chr hi)

let print_nfa_dot write_label write_dec oc nfa =
  let print_q oc {id=id;label={n_label=nlabel; epsilon=eps};map=map;dec=dec} =
    if id >= 0 then (
      fprintf oc "S%d [label=\"%d\"]\n" id id;
      IMap.iter_range (fun lo hi dests ->
	Set.iter (fun d -> if d >= 0 then
	    fprintf oc "S%d -> S%d [label=\"%a\"]\n" id d print_label (lo,hi)) dests
      ) map;
      Set.iter (fun d -> if d >= 0 then
	  fprintf oc "S%d -> S%d [label=\"..\"]\n" id d
      ) eps;
    )
  in
  fprintf oc "digraph nfa {\n";
  print_fa ~ids:false print_q oc nfa;
  fprintf oc "}\n"

let print_dec oc dec = if dec <> [] then List.print Int.print oc dec

let print_dot_dfa ~id ~print_dec oc dfa =
  let print_q oc i {label=_label; map=map; dec=dec; id=q_id} =
    fprintf oc "%s%d [label=\"%dx%d " id i i q_id;
    print_dec oc dec;
    fprintf oc "\"];\n";
    let trans =
      IMap.fold_range (fun lo hi q acc -> MultiPMap.add q (lo,hi) acc)
	map (MultiPMap.create Int.compare Tuple2.compare) in
    MultiPMap.iter (fun q lhset ->
		      fprintf oc "%s%d -> %s%d [label=\"" id i id q;
		      Set.print ~first:"" ~last:"" ~sep:" " print_rng oc lhset;
		      fprintf oc "\"];") trans;
    fprintf oc "\n"
  in
  fprintf oc "digraph %s {\n" id;
  Array.iteri (print_q oc) dfa.qs;
  fprintf oc "}\n"

let print_dfa_x _ ~id oc d = print_dot_dfa ~print_dec ~id oc d

let count_qs f qs = Array.enum qs |> map f |> Enum.sum

let summarize_dfa ~id oc dfa =
  let tr_count = count_qs (fun q -> IMap.enum q.map |> Enum.count) dfa.qs in
  fprintf oc "#DFA %s: %d states, %d transition ranges\n" id (Array.length dfa.qs) tr_count;
(*
  let finals = Array.fold_left (fun a q -> if q.dec = [] then a else q.dec :: a) [] dfa.qs in
List.print ~last:"]\n" (List.print Int.print) oc finals;
*)
  ()

(*let max_depth = Value.observe_int_ref "Depth (Max)" (ref 0) *)

let build_dfa ?(labels=false) dec_rules reg =
  let new_id = ref (fun _ _ -> assert false) in (* hole for recursion *)
  let id_map = map_id_set ~comp:Minreg.compare ~min_id:0 (fun x id -> !new_id x id) in
  let states = ref Vect.empty in
  let make_node get_id r id =
  (*  Printf.eprintf "#Node making from regex: '%a'\n(%s)\n%!" Minreg.printp r (dump r); *)
    let (dec, dt_reg) = canonize dec_rules r in
(*    if id mod 100 = 1 then eprintf "N %d @ %.2f\n%!" id (Sys.time ()); *)
    (* turn reg IMap.t into state IMap.t *)
    let map = IMap.map (fun r -> Id.to_int (get_id r)) dt_reg in
    let q = {label=if labels then r else epsilon; id=id; map=map; dec=dec} in
    vect_set_any states id q;
    () (* don't store any value in the map *)
  in
  new_id := make_node;  (* close recursion *)
  (* make all the state nodes, magically *)
  let q0 = Id.to_int (id_map.get_id reg) in
  let qs = Vect.map Option.get !states |> Vect.to_array in
(*  eprintf "\n#Built DFA with %d states.\n" (Array.length qs); *)
  {qs = qs; q0 = qs.(q0)} |> check_ids
;;

(* let build_dfa ?labels reg = log_f "Building DFA" (build_dfa ?labels) reg *)

let cmp_q q1 q2 = Int.compare q1.id q2.id
let debug_nfacon = false
let build_nfa (dec0, of_dec, _) reg =
  let get_idx = make_counter 0 in
  let qs = ref Vect.empty in
  let new_state ?(id=get_idx()) ?(n_label=None) ?(epsilon=Set.empty)
      ?(map=IMap.empty ~eq:Set.equal) ?(dec=dec0) () =
(*    if idx mod 100 = 1 then eprintf "N %d @ %.2f\n%!" idx (Sys.time ()); *)
    {label={n_label;epsilon};map;dec;id} |> tap (vect_set_any qs id)
  in
  let dest q = Set.singleton ~cmp:Int.compare q.id in
  let dests ql = List.enum ql |> map (fun x -> x.id) |> Set.of_enum_cmp ~cmp:Int.compare in
  let final q = Set.singleton ~cmp:cmp_q q in
  let add_eps dst q =
    if not (Set.is_empty q.label.epsilon) then failwith "nonempty epsilon";
    q.label.epsilon <- Set.union q.label.epsilon (dest dst) in
  let dup q = q, final q in
  let gen_map v dst = IMap.set_to_map ~eq:Set.equal v dst in
  let no_finals = Set.create cmp_q in
  let rec loop = function
    | Value v -> if debug_nfacon then printf "v ";
      let out_q = new_state () in
      let in_q = new_state ~map:(gen_map v (dest out_q)) () in
      in_q,final out_q
    | Accept id -> if debug_nfacon then printf "a "; new_state ~dec:(of_dec id) () |> dup
    | Union rl -> if debug_nfacon then printf "u%d " (Set.cardinal rl);
      let ins,fins = Set.enum rl |> map loop |> List.of_enum |> List.split in
      let in_q = new_state ~epsilon:(dests ins) () in
      in_q, List.fold_left Set.union no_finals fins
    | Kleene (Value v) -> if debug_nfacon then printf "kv "; (* special case looping states *)
      let id = get_idx () in
      new_state ~id ~map:(gen_map v (Set.singleton id)) () |> dup
    | Kleene r -> if debug_nfacon then printf "k ";
      let in1,final1 = loop r in
      let in0 = new_state ~epsilon:(Set.singleton in1.id) () in
      Set.iter (add_eps in0) final1;
      in0,final in0
    | Concat ([],_) -> if debug_nfacon then printf "c0 ";
      new_state (), Set.create cmp_q
    | Concat ([rx], _red) -> if debug_nfacon then printf "c1 "; loop rx
    | Concat (Value v::t,_red) -> if debug_nfacon then printf "cv ";
      let in1,finals = loop (Concat (t,_red)) in
      new_state ~map:(gen_map v (dest in1)) (), finals
    | Concat (rx::t,_red) -> if debug_nfacon then printf "c+ ";
      let in0,finals0 = loop rx in
      let in1,finals1 = loop (Concat (t, _red)) in
      if debug_nfacon then printf "+%d " (Set.cardinal finals0);
      Set.iter (add_eps in1) finals0;
      in0, finals1
  in
  let q0, _ = loop reg in
  let qs = Vect.map Option.get !qs |> Vect.to_array in
  ({qs=qs; q0=q0} : ('a,'b) nfa)

let build_nfa_orig (dec0, of_dec, _) reg =
  let get_idx = make_counter 0 in
  let qs = ref Vect.empty in
  let new_state ?(label=None) ?(epsilon=Set.empty)
      ?(map=IMap.empty ~eq:Set.equal) ?(dec=dec0) () =
    let idx = get_idx () in
(*    if idx mod 100 = 1 then eprintf "N %d @ %.2f\n%!" idx (Sys.time ()); *)
    let q = { label = {n_label = label; epsilon = epsilon};
     map = map; dec = dec; id = idx} in
    vect_set_any qs idx q;
    q
  in
  let dup x = (x,x) in
  let rec loop = function
    | Value v -> let out_q = new_state () in let in_q = new_state ~map:(IMap.set_to_map v (Set.singleton out_q.id)) () in in_q,out_q
    | Accept id -> new_state ~dec:(of_dec id) () |> dup
    | Union rl ->
      let ins,outs =
	Set.enum rl |> List.of_enum |> List.map loop |> List.split
      in
      let in_q = new_state ~epsilon:(List.map (fun x -> x.id) ins|> List.enum |> Set.of_enum) () in
      let out_q = new_state () in
      let eps = Set.singleton out_q.id in
      List.iter (fun oi -> oi.label.epsilon <- eps) outs;
      in_q, out_q
    | Kleene r ->
      let in1,out1 = loop r in
      let out0 = new_state () in
      let in0 = new_state ~epsilon:(Set.singleton in1.id |> Set.add out0.id) () in
      out1.label.epsilon <- (Set.singleton in0.id);
      in0,out0
    | Concat ([],_) -> new_state () |> dup
    | Concat (Value v::t,_red) ->
      let in1,out1 = loop (Concat (t,_red)) in
      new_state ~map:(IMap.set_to_map v (Set.singleton in1.id)) (), out1
    | Concat (rx::t,_red) ->
      let in0,out0 = loop rx in
      let in1,out1 = loop (Concat (t, _red)) in
      out0.label.epsilon <- (Set.singleton in1.id);
      in0, out1
  in
  let q0, _ = loop reg in
  let qs = Vect.map Option.get !qs |> Vect.to_array in
  ({qs=qs; q0=q0} : ('a,'b) nfa)

let merge_iset = Set.union (*(List.rev_append a b) |> List.sort_unique Int.compare *)

let merge_nfa_maps m1 m2 = IMap.union Set.union m1 m2

type hmap_status = Unmade | In_progress | No_change | Done of qset IMap.t * qset

let simplify_nfa nfa = (* remove in-epsilon-only states *)
  let remove = Array.create (size nfa) true in
  let set_unremovable d = remove.(d) <- false in
  let set_targets_unremovable q =
    IMap.iter (fun _c dsts -> Set.iter set_unremovable dsts) q.map
  in
  let hoisted_maps = Array.create (size nfa) Unmade in
  let merge_hmap i (m,e) = match hoisted_maps.(i) with
    | In_progress -> m,e
    | No_change -> let q = nfa.qs.(i) in
		   (merge_nfa_maps m q.map), (merge_iset e q.label.epsilon)
    | Done (m2,e2) ->  (merge_nfa_maps m m2), (merge_iset e e2)
    | Unmade -> assert false
  in
  let rec hoist_removed_targets i =
    match hoisted_maps.(i) with
      |	Done _ | In_progress | No_change -> ()
      | Unmade ->
	hoisted_maps.(i) <- In_progress;
	let to_hoist = ref Set.empty in
	IMap.iter_range (fun _ _ dst ->
	  to_hoist := Set.union (Set.filter (fun i -> remove.(i)) dst) !to_hoist)
	    nfa.qs.(i).map;
	let eps_remove, eps_keep = Set.partition (fun i -> remove.(i)) nfa.qs.(i).label.epsilon in
	to_hoist := Set.union eps_remove !to_hoist;
	if Set.is_empty !to_hoist then
	  hoisted_maps.(i) <- No_change
	else begin
	  Set.iter hoist_removed_targets !to_hoist;
	  let m,e = Set.fold merge_hmap !to_hoist (nfa.qs.(i).map,eps_keep) in
	  hoisted_maps.(i) <- Done (m,e)
	end
  in
  let null_q = {id=(-1); map=IMap.empty ~eq:Set.equal; dec=nfa.q0.dec;
		label={n_label=nfa.q0.label.n_label; epsilon=Set.empty};}  in
  let q_with_hoisted_map q =
    match hoisted_maps.(q.id),remove.(q.id) with
      | Unmade,_ | In_progress,_ -> assert false
      | _, true -> null_q
      | No_change,false -> q
      | Done (m,e),false->
	{q with map = m; label={q.label with epsilon = e}}
  in
  (* don't remove start state *)
  remove.(nfa.q0.id) <- false;
  (* mark removable states *)
  Array.iter set_targets_unremovable nfa.qs;
  let num_to_remove = Array.filter identity remove |> Array.length in
  printf "Simplify_nfa: removing %d of %d nfa states\n" num_to_remove (size nfa);
  iter hoist_removed_targets (Array.range hoisted_maps);
  map_qs q_with_hoisted_map nfa

let get_eps_closure nfa n_id =
  let rec loop acc added =
    let add_epsilon n acc =
      Set.fold Set.add nfa.qs.(n).label.epsilon acc
    in
    let all = Set.fold add_epsilon added acc in
    let added = Set.diff all acc in
    if Set.is_empty added then acc
    else loop all added
  in
  let n_ids = (Set.singleton n_id) in
  loop n_ids n_ids

let close_transitions nfa =
  let q_with_closed_map q =
    let new_map = IMap.map ~eq:Set.equal (fun dsts -> Set.enum dsts |> map (get_eps_closure nfa) |> Enum.reduce Set.union ) q.map in
    {q with map=new_map}
  in
  map_qs q_with_closed_map nfa

let build_dfa_via_nfa ~labels (dec0, of_dec, dec_merge as dec_rules) reg =
  ignore labels;
  let nfa = build_nfa dec_rules reg |> simplify_nfa |> close_transitions in
  printf "NFA built %.3f (%d states)\n%!" (Sys.time()) (Array.length nfa.qs);
  (* let print_nfa_label oc l = () in
     let print_nfa_dec oc d = () in
     printf "NFA: \n%a" (print_nfa print_nfa_label print_nfa_dec) nfa;
     printf "q0: %d\n" nfa.q0.id; *)
  let states = ref Vect.empty in
  let make_node get_id ns id =
(*    eprintf "Making state %d for %a\n%!" id  ns; *)
    (* get the transitions for that character from the nfa *)
    if id mod 100 = 1 then eprintf "N %d @ %.2f\n%!" id (Sys.time ());
    let map =
      Set.fold (fun n acc -> merge_nfa_maps acc nfa.qs.(n).map) ns (IMap.empty ~eq:Set.equal)
      |> IMap.map (get_id |- Id.to_int)
    in
    let dec =
      Set.fold (fun n acc -> dec_merge acc nfa.qs.(n).dec) ns dec0
    in
    let q = {label = ns; id=id; map=map; dec=dec} in
    vect_set_any states id q;
    ()
  in
  let set_compare s1 s2 = Enum.compare Int.compare (Set.enum s1) (Set.enum s2) in
  let id_map = map_id_set ~comp:set_compare ~min_id:0 make_node in
  let q0 = get_eps_closure nfa nfa.q0.id |> id_map.get_id |> Id.to_int in
  let qs = Vect.map Option.get !states |> Vect.to_array in
  {qs=qs; q0=qs.(q0)} |> check_ids

let print_int_range oc x y =
  if y > x then fprintf oc "%d-%d " x y else fprintf oc "%d " x

let reachable {qs=qs; q0=s0} =
  let rec loop reached news =
    let reached = ISet.union reached news in
(*    print_string "Reached: "; ISet.iter_range (print_int_range stdout) reached; print_newline ();  *)
    (* build the set of next hops from a node *)
    let nexts q = IMap.fold_range (fun _ _ -> ISet.add) qs.(q).map ISet.empty in
    let next = ISet.fold (fun i acc -> ISet.union acc (nexts i)) news ISet.empty in
(* print_string "Next: "; ISet.iter_range (print_int_range stdout) next; print_newline ();  *)
    let news = ISet.diff next reached in
    if ISet.is_empty news then reached else loop reached news
  in
  loop ISet.empty (ISet.singleton s0.id)

let reachable x = log_f "Reachable" reachable x

let remove_unreachable dfa =
  let keep = reachable dfa |> ISet.elements |> Array.of_list in
(*   printf "#Reachable states: %d\n%!" (Array.length keep); *)
  let n = Array.length dfa.qs in
  let rep_state = Array.make n (-1) in
  Array.iteri (fun i r -> rep_state.(r) <- i) keep;
  let mod_tr tr = IMap.fold_range (fun lo hi q acc -> if rep_state.(q) = -1 then assert false else IMap.add_range lo hi rep_state.(q) acc) tr (IMap.empty ~eq:Int.eq)in
  let mod_state pos i = {dfa.qs.(i) with map = mod_tr dfa.qs.(i).map; id = pos} in
  let qs = Array.mapi mod_state keep in
(*  let mod_state i = {dfa.qs.(i) with map = mod_tr dfa.qs.(i).map} in
  let qs = Array.map mod_state keep in *)
  { qs = qs; q0 = qs.(rep_state.(dfa.q0.id)) } |> check_ids

let remove_unreachable x = log_f "Remove Unreachable" remove_unreachable x

let quotient rep {qs=qs; q0=q0} =
  let n = Array.length qs in
  (* what elements need to be kept as representatives *)
  let range = Enum.fold (fun a i -> ISet.add (rep i) a) ISet.empty (0--^n)
	      |> ISet.elements |> Array.of_list in
  let rep_state = Array.make n (-1) in
  (* range states get mapped to their position *)
  Array.iteri (fun i r -> rep_state.(r) <- i) range;
  (* redundant states get mapped to their rep's state *)
  Enum.iter (fun i -> rep_state.(i) <- rep_state.(rep i)) (0--^n);
  let mod_tr tr = IMap.map (fun i -> rep_state.(i)) tr in
  let mod_state pos i = {qs.(i) with map = mod_tr qs.(i).map; id = pos} in
  let qs = Array.mapi mod_state range in
  { qs = qs; q0 = qs.(rep_state.(q0.id)) } |> check_ids

(* let quotient x = log_f "Quotient" quotient x *)

let print_matrix m2 =
  printf "     ";
  Array.iteri (fun i _ -> printf "%3d " i) m2;
  printf "\n";
  Array.iteri (fun i r ->
 		 printf "%3d) " i;
		 Array.iter (fun v -> printf "%3d " v) r;
		 printf "\n";
	      ) m2

let print_bmatrix n m =
  Enum.iter (fun i ->
 		 printf "#%2d) " i;
		 Enum.iter (fun j -> print_string (if BitSet.mem m (i*n+j) then "1" else "0")) (0--^n);
		 printf "\n";
	      ) (0--^n)

let commonality ?(eq = (=)) q1 q2 =
  let same_dec lo hi d1 d2 acc =
    match d1, d2 with
	Some q1, Some q2 when eq q1 q2 -> acc+(hi-lo+1)
      | _ -> acc
  in
  IMap.fold2_range same_dec q1.map q2.map 0

let difference ?(eq = (=)) q1 q2 =
  let diff_dec lo hi d1 d2 acc =
    match d1,d2 with
	Some q1, Some q2 when eq q1 q2 -> acc
      | None, None -> assert false
      | _ -> acc + (hi-lo+1)
  in
  IMap.fold2_range diff_dec q1.map q2.map 0

let is_same ?(eq = (=)) q1 q2 =
  let diff_dec _lo _hi d1 d2 =
    match d1,d2 with
	Some q1, Some q2 when eq q1 q2 -> true
      | None, None -> assert false
      | _ -> false
  in
  IMap.forall2_range diff_dec q1.map q2.map

(* let pass = Value.observe_int_ref "dist pass" (ref 0) *)

let dist_test dfa =
  let n = Array.length dfa.qs in

(* POSSIBLE OPTIMIZATION FOR DEPENDENCIES
  let edge_in = Array.make n [] in
  Array.iteri (fun i qi -> IMap.iter_range
		(fun _ _ j ->
		   edge_in.(j) <- i :: edge_in.(j)
		) qi.map) dfa.qs;
*)

(* SOME CODE FROM fjavac project *)
  let m = BitSet.create_full (n*n) in
  let pos i j = i * n + j in
  let eq i j = BitSet.mem m (pos i j) in
  let set_not_eq i j = BitSet.unset m (pos i j); BitSet.unset m (pos j i) in

  for i = 0 to n-1 do
    for j = i+1 to n-1 do
      (* states with different finalness are unequal *)
      if dfa.qs.(i).dec <> dfa.qs.(j).dec then set_not_eq i j
    done
  done;
  (*  print_bmatrix n m;   *)
  let more = ref true in
  while !more do
    more := false;
    for i = 0 to n-1 do
      for j = i+1 to n-1 do(* distinct pairs (i,j) *)
        if eq i j then     (* only check if some equal states aren't *)
	  (* if on some a, these two map to non-same states, then they're
	     distinguishable *)
	  let same = is_same ~eq dfa.qs.(i) dfa.qs.(j) in
(*	  printf "D(%d,%d) = %d " i j diff;   *)
	  if not same then ( set_not_eq i j; more := true; )
      done;
    done;
    (*    print_bmatrix n m;  *)
  done;
  m

let dist_test x = log_f "Dist Test" dist_test x

let print_diffs rep dfa =
  let print_d i q =
    let j = rep i in
    if j <> i then begin
      printf "#Node %d replaced by %d:\n" i j;
      printf "#%d: " i; Minreg.print stdout q.label; print_newline();
      print_tmap stdout q.map; print_newline();
      print_tmap stdout (IMap.map rep q.map); print_newline();

      printf "#%d: " j; Minreg.print stdout dfa.qs.(j).label; print_newline();
      print_tmap stdout dfa.qs.(j).map; print_newline();
      print_tmap stdout (IMap.map rep dfa.qs.(j).map); print_newline();
      print_newline();
    end
  in
  Array.iteri print_d dfa.qs

let minimize dfa =
  let dfa = remove_unreachable dfa in
  let m = dist_test dfa in (* returns a matrix of state equivalences *)
  (* first state equal to each state *)
  let n = Array.length dfa.qs in
  let rep i = Enum.find (fun j -> BitSet.mem m (i*n+j)) (0--^n) in
(*  print_diffs rep dfa; *)
  quotient rep dfa

(*let minimize dfa =
  let ret = minimize dfa in
  eprintf "Minimized-dfa: %a" (summarize_dfa ~id:"dfa") ret;
  ret
*)

(* runs the dfa on the entire enum - produces the trace of all states
gone through *)
let run_dfa_trace dfa enum =
  let next_q q c =
    match q with None -> None | Some q ->
      try Some(IMap.find (Char.code c) dfa.qs.(q).map) with Not_found -> None
  in
  scanl next_q (Some dfa.q0.id) enum

let get_dec dfa qid = Option.map (fun q -> dfa.qs.(q).dec) qid
(* runs a dfa *)

let run_dfa_dec dfa e = run_dfa_trace dfa e |> Enum.reduce (fun _ b -> b) |> get_dec dfa

let run_dfa_stream dfa enum =
  let rec next_q qi =
    match dfa.qs.(qi).dec with
      | Some dec -> dec
      | None -> match Enum.get enum with
	    None -> failwith "End of stream reached without match"
	  | Some (_,c) ->
	      try IMap.find (Char.code c) dfa.qs.(qi).map |> next_q
	      with Not_found ->
		failwith (sprintf "Character %c has no transition at state %d" c qi)
  in
  next_q dfa.q0.id

let print_trace oc dfa trace =
  let last = Enum.reduce (fun _ y -> y) (Enum.clone trace) in
  let qopt_to_str = function None -> "X" | Some q -> string_of_int q in
  let qopt_to_dec_l = function None -> [] | Some q -> dfa.qs.(q).dec in
  fprintf oc "%a: %a\n"
    (Enum.print (fun oc qo -> IO.nwrite oc (qopt_to_str qo))) trace
    (List.print Int.print) (qopt_to_dec_l last);
  ()
