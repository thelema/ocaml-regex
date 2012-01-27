(*
Gc.full_major ();;
*)

open Batteries
open Ean_std
open Printf

type state_id
type class_id
type state_pos

external to_int : 'a -> int = "%identity"
external of_int : int -> 'a = "%identity"
(*
let to_int x = x
let of_int x = x
 *)
let pprint oc x = Int.print oc (to_int x)

let hopcroft dfa =
  (* initialisation des structures*)

  let cardinal_sigma = Regex_dfa.num_chars in
  let cardinal_q=Regex_dfa.size dfa in
  (*nombre d'etats*)

  let transition_inverse= 
    (Array.make_matrix cardinal_sigma cardinal_q ([] : state_id list)) 
  in
  for i=0 to (cardinal_q-1) do
    for j=0 to (cardinal_sigma-1) do
      try 
	let succ=IMap.find j dfa.Regex_dfa.qs.(i).Regex_dfa.map in
	transition_inverse.(j).(succ) <- (of_int i) :: transition_inverse.(j).(succ)
      with Not_found -> ()
    done
  done;
  (* construct the inverse of the transition table :
     char, state -> previous state list *)

  let table_etat_classe=Array.create cardinal_q (of_int 0) in
  (* state_pos -> class
     table_etat_classe.(q) = class of state q
   *)

  let tableau_etat = Array.init cardinal_q (fun _ -> of_int (-1)) in (* pos -> state *)
  let tableau_etat_inv = Array.init cardinal_q (fun _ -> of_int (-1)) in (* state -> pos *)
  (* tableau_etat allows us to reorder the states  *)

  let table_classe_liste= DynArray.make 512 in
  (* Which nodes in tableau_etat are in which class
     
     Array of classes, with (lo,hi) range values of where that class
     is located in tableau_etat. *)

  let table_pointeur_classe_liste= DynArray.make 512 in
  (* indexed by class numbers, this gives the cut point of each class.
     The cut point starts at the end of the class, and elements are
     swapped to it and the cut point moved down to allow cutting
     classes.  *)

  let work_queue = Stack.create () in

  (* helper functions *)
  let get_state_of_pos : state_pos -> state_id =
    fun p -> tableau_etat.(p|>to_int) in
  let get_pos_of_state : state_id -> state_pos =
    fun q -> tableau_etat_inv.(q|>to_int) in
  let get_class : state_id -> class_id = 
    fun q -> table_etat_classe.(q |> to_int) in
  let set_class : state_id -> class_id -> unit =
    fun q c -> table_etat_classe.(q|> to_int) <- c in
  let set_class_pos : state_pos -> class_id -> unit =
    fun q c -> table_etat_classe.(get_state_of_pos q|> to_int) <- c in
  let get_class_range : class_id -> state_pos * state_pos =
    fun c -> DynArray.get table_classe_liste (to_int c) in
  let get_tail : class_id -> state_pos =
    fun c -> DynArray.get table_pointeur_classe_liste (to_int c) in
  let set_tail : class_id -> state_pos -> unit =
    fun c p -> DynArray.set table_pointeur_classe_liste (to_int c) p in      

  let set_class_range c lo hi =
    DynArray.set table_classe_liste (to_int c) (lo,hi);
    set_tail c hi
  in
  let new_class lo hi =
    let new_class_id = DynArray.length table_classe_liste |> of_int in
    DynArray.add table_classe_liste (lo,hi);
    DynArray.add table_pointeur_classe_liste hi;
    for j = (to_int lo) to (to_int hi) do
      set_class_pos (of_int j) new_class_id
    done;
    (new_class_id : class_id)
  in      

  let echange (indice1:state_pos) (indice2:state_pos)=
    let elt1=tableau_etat.(indice1|>to_int) in
    let elt2=tableau_etat.(indice2|>to_int) in
    tableau_etat_inv.(elt1|>to_int)<-indice2;
    tableau_etat_inv.(elt2|>to_int)<-indice1;
    tableau_etat.(indice1|>to_int)<-elt2;
    tableau_etat.(indice2|>to_int)<-elt1 
  in
  (*Fonction permettant d'echanger les elements d'indice indice1 et indice2 d
    ans le tableau tableau_etat et mise à jour du tableau tableau_etat_inv *)

  let print_tableau oc =
    Array.print ~first:"te  " ~last:"|]\n" pprint oc tableau_etat;
    Array.print ~first:"tec " ~last:"|]\n" pprint oc table_etat_classe;
    Array.print ~first:"tei " ~last:"|]\n" pprint oc tableau_etat_inv;


    DynArray.print ~last:"]\n" (Pair.print2 pprint) oc table_classe_liste;
    DynArray.print ~last:"]\n" pprint oc table_pointeur_classe_liste;
  in

  let _verify_tableau () = 
    for i = 0 to cardinal_q-1 do
      assert (tableau_etat.(tableau_etat_inv.(i)|>to_int)|>to_int = i);
      assert (tableau_etat_inv.(tableau_etat.(i)|>to_int)|>to_int = i);
    done;

    let tcl_len = DynArray.length table_classe_liste 
    and tpcl_len = DynArray.length table_pointeur_classe_liste in
    assert (tcl_len = tpcl_len);
    for i = 0 to tcl_len-1 do
      let i = of_int i in
      let _l,h = get_class_range i in
      assert (get_tail i = h);
    done;
      
    for q = 0 to cardinal_q-1 do
      let q = of_int q in
      let c = get_class q in
      let l,h = get_class_range c in
      let p = get_pos_of_state q in
      if p < l || p > h then (
	printf "wrong pos: state %d in class %a (%a,%a) has pos %a\n" 
	  q pprint c pprint l pprint h pprint p;
	print_tableau stderr;
	assert false;
      )
    done;
  in


  (****** BUILD INITIAL PARTITION ******)
  ( 
    let m =  (* MultiMap from decisions to state numbers *)
      Array.fold_lefti (fun acc i n -> MultiPMap.add n.Regex_dfa.dec (of_int i) acc) 
	MultiPMap.empty dfa.Regex_dfa.qs
    in
    
    let next_class_id = ref 0 in
    let next_free_pos = ref 0 in
    let decs = ref [] in
    let gen_class d qset =
(*      PSet.print ~first:"Partition: [" ~sep:"," ~last:"]\n" pprint stdout qset; *)
      let lo = !next_free_pos |> of_int in
      PSet.iter (fun (q:state_id) -> (* put those states in the tableau_etat *)
	tableau_etat.(!next_free_pos) <- q;
	tableau_etat_inv.(to_int q) <- !next_free_pos |> of_int; 
	incr next_free_pos) qset;
      let hi = !next_free_pos - 1 |> of_int in

      DynArray.add table_classe_liste (lo,hi);
      DynArray.add table_pointeur_classe_liste hi;
      
      let i = !next_class_id |> of_int in
      incr next_class_id;
      decs := (d,i) :: !decs; (* save the decision and its id *)
      PSet.iter (fun q -> set_class q i) qset; (* set those states' class *)
    in
    MultiPMap.iter gen_class m;
    
    (* push all but the largest partition onto the work queue *)
    let max_dec,_ = 
      maxarg (fun (d,_) -> MultiPMap.find d m |> PSet.cardinal) (List.enum !decs)
    in
    let push_non_max (d,id) = if d <> max_dec then Stack.push id work_queue in
    List.iter push_non_max !decs;

  );
  (****** DONE BUILDING PARTITION ******)


  let split_broken_class h =
    let (i1,i2) = get_class_range h in
    let cut_point = get_tail h |> to_int in
(*    printf "split_broken_class %a (%a,%a @%a)\n" pprint h pprint i1 pprint i2 pprint cut_point; *)
    if cut_point = (to_int i1)-1 (* no split - all elements in new class *)
    then set_tail h i2
    else
      let new_class_id = 
	if (to_int i2)-cut_point-1 <= cut_point-(to_int i1) then begin
	  (* new class is top half of partition *)
	  set_class_range h i1 (of_int cut_point);
	  new_class (cut_point+1|>of_int) i2
	end else begin
	  (* new class is bottom half of partition *)
	  set_class_range h (cut_point+1|>of_int) i2;
	  new_class i1 (of_int cut_point)
	end
      in
      Stack.push new_class_id work_queue;
  in

  (* swap this node to the tail of its class and decrement the tail pointer *)
  let swap_to_class_tail (c:class_id) (x:state_id) = 
    let indice_x = get_pos_of_state x in
    let pointeur = get_tail c in
(*printf "moving %a from %a to %a\n" pprint x pprint indice_x pprint pointeur; *)
    echange indice_x pointeur;
    set_tail c (to_int pointeur - 1 |> of_int)
  in

  let broken_classes=ref [] in
  let antecedents_dans_c=ref [] in

  let split_class ~except x = (* x is an original state (from transition_inverse) *)
    let classe_x = get_class x in
    if classe_x = except then (* have to swap around c's elements last *)
      antecedents_dans_c := x :: !antecedents_dans_c
    else
      let (i1,i2) = get_class_range classe_x in
      if i1 <> i2 then (* if the class has more than one element *)
	let pointeur = get_tail classe_x in
	if pointeur=i2 then ((* first time we break this class *)
	  broken_classes:= classe_x :: !broken_classes;
(*	  printf "Breaking class %a\n" pprint classe_x; *)
	);
(*	printf "In class %a (%a,%a c%a) " pprint classe_x pprint i1 pprint i2 pprint pointeur; *)
	swap_to_class_tail classe_x x
  in

  (*Fonctions de minimisation*)
  (** @param c class to split preimage of
      @param a character to test for differences *)
  let casse_par_rapport (c:class_id) a =
    broken_classes := [];
    antecedents_dans_c := [];

    let (j1,j2) = get_class_range c in
    (* for each state_pos l in the class c, move those states which
       transition to l on a past the tail of their class *)
    for l = to_int j1 to to_int j2 do
      let l = of_int l in
      List.iter (split_class ~except:c) 
	transition_inverse.(a).(get_state_of_pos l|>to_int)
    done;

    (* check if we broke c *)
    if !antecedents_dans_c <> [] then 
      broken_classes:= c:: !broken_classes;
    
    List.iter (swap_to_class_tail c) !antecedents_dans_c;

    (* break classes based on table_pointeur_classe_liste *)
    List.iter split_broken_class !broken_classes;

(*    verify_tableau(); *)
  in
  
  (* Main work loop *)
  while not (Stack.is_empty work_queue) do
    let target_class = Stack.pop work_queue in
(*    printf "Splitting on class %a\n" pprint target_class; *)
    for letter=0 to cardinal_sigma-1 do
      casse_par_rapport target_class letter
    done
  done;
(*printf "done\n%!"; *)

  (* return the representative state function *)
  (fun q -> let c = get_class (of_int q) in let i,_ = get_class_range c in get_state_of_pos i |> to_int)

let minimize dfa =
  let rep = hopcroft dfa in
  Regex_dfa.quotient rep dfa
