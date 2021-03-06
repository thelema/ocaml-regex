(* Minimizing regex library - identical to pcregex's regex type,
   except has a boolean of whether that subtree is reduced *)

open Batteries
open Printf

(* BEGIN MIN_REGEX *)

type 'a t =
  | Union of 'a t Set.t
  | Concat of 'a t list * bool
  | Kleene of 'a t
  | Value of ISet.t
  | Accept of 'a

let epsilon = Concat ([],true)

let rec compare ?(dec_comp=Pervasives.compare) x y = match (x,y) with
    Union a, Union b -> Enum.compare compare (Set.enum a) (Set.enum b)
  | Accept a, Accept b -> dec_comp a b
  | a,b -> Pervasives.compare a b

let eq ?dec_comp x y =
  compare ?dec_comp x y = 0

let rec concat_elim acc = function
    [] -> List.rev acc
  | Concat (x,_) :: t -> concat_elim acc (x@t)
  | h :: t -> concat_elim (h::acc) t

let rec reduce = function
  | Union s when Set.cardinal s = 1 -> Set.choose s
  | Union _ as e -> e
  | Concat (_,true) as e -> e
  | Concat ([],_) -> Concat ([],true)
  | Concat ([x],_) -> reduce x
  | Concat (l,false) -> Concat (concat_elim [] l |> List.map reduce, true)
  | Kleene x -> Kleene (reduce x)
  | Value _ as e -> e
  | Accept _ as e -> e

let append t u = Concat (u::t, false)
let union s = Union (Set.map reduce s)
let union_unsafe s = Union s
let union2 a b = Union (Set.add (reduce a) (Set.singleton (reduce b))) |> reduce
let union_with s = function
    Union s1 -> Union (Set.union s s1)
  | e -> Union (Set.add (reduce e) s)
let union_sets s1 s2 = Union (Set.union s1 s2)
let concat l = Concat (l,false)
let concat_unsafe l = Concat (l,true)

let reduce_union t1 t2 =
  match reduce t1, reduce t2 with
    | Union a, Union b -> union_sets a b
    | Union a, b | b, Union a -> Union (Set.add b a)
    | a, b -> Union (Set.add a (Set.singleton b))

let roots = Hashtbl.create 10

let add_root rx str = Hashtbl.add roots rx str

let rec print oc = function
  | x when Hashtbl.mem roots x -> IO.nwrite oc (Hashtbl.find roots x)
  | Union s when Set.mem epsilon s -> print oc (Union (Set.remove epsilon s)); IO.write oc '?'
  | Union s -> Set.print ~first:"(" ~sep:"|" ~last:")" print oc s
  | Concat ([], _) -> ()
  | Concat (h::t,_) -> print oc h; print oc (Concat (t,true))
  | Kleene (Concat (regl,_)) -> List.print ~first:"(" ~sep:"" ~last:")" print oc regl;  IO.write oc '*'
  | Kleene reg -> print oc reg; IO.write oc '*'
  | Value a -> Pcregex.print_iset oc a
  | Accept i -> fprintf oc "{{%d}}" i

let rec printp ?(dec=true) oc = function
  | Union s when Set.mem epsilon s -> printp oc (Union (Set.remove epsilon s)); IO.write oc '?'
  | Union s -> Set.print ~first:"(" ~sep:"|" ~last:")" printp oc s
  | Concat ([], _) -> ()
  | Concat (h::t,_) -> printp oc h; printp oc (Concat (t,true))
  | Kleene (Concat (regl,_)) -> List.print ~first:"(" ~sep:"" ~last:")" printp oc regl;  IO.write oc '*'
  | Kleene reg -> printp oc reg; IO.write oc '*'
  | Value a -> Pcregex.print_iset oc a
  | Accept x -> fprintf oc "{{%s}}" (if dec then dump x else "x")


let print_inner_norm_regex oc rmap =
   IO.write oc '(';
   IMap.iter_range (Ean_std.print_range print oc) rmap;
   IO.write oc ')'

let print_norm_regex oc (_acc, rmap) = print_inner_norm_regex oc rmap

let print_norm_regexp oc (_, rmap) =
   IO.write oc '(';
   IMap.iter_range (Ean_std.print_range printp oc) rmap;
   IO.write oc ')'

(* let red_p = Point.create "MReduce" *)
(* let red_t = Time.create "MReduce" *)
(* let reduce x =  *)
(*   Point.observe red_p;  *)
(*   Time.start red_t;  *)
(* (\*  printf "#RXPRE:%a\n" print_mregex x;  *\) *)
(*   let r = reduce x in  *)
(*   Time.stop red_t;  *)
(* (\*  printf "#RXPST:%a\n" print_mregex x;  *\) *)
(*   r *)

let rec tag_red = function
  | Pcregex.Union l -> Union (List.fold_left (fun acc e -> Set.add (tag_red e) acc) Set.empty l)
  | Pcregex.Concat l -> Concat (List.map tag_red l,true)
  | Pcregex.Kleene r -> Kleene (tag_red r)
  | Pcregex.Value a -> Value a
  | Pcregex.Accept i -> Accept i

let of_reg reg = Pcregex.reduce reg |> tag_red

let hash x = Hashtbl.hash (IO.to_string print x)

let rec depth = function
  | Value _ -> 1
  | Accept _ -> 1
  | Kleene x -> 1 + depth x
  | Union s -> 1 + (Set.enum s |> map depth |> Enum.reduce max)
  | Concat (l,_) -> 1 + (List.enum l |> map depth |> Enum.reduce max)

let rec width = function
  | Value _ -> 1
  | Accept _ -> 1
  | Kleene x -> max 1 (width x)
  | Union s -> max (Set.cardinal s) (Set.enum s |> map width |> Enum.reduce max)
  | Concat ([], _) -> 0
  | Concat (l,_) -> max (List.length l) (List.enum l |> map width |> Enum.reduce max)


let rec factor_rxs rxs =
  if Set.is_empty rxs || Set.cardinal rxs = 1 then rxs else
    match Set.choose rxs with
      | Concat (rxh::rxt,_) ->
	let put_in_group rx (tls,rst) = match rx with
	  | Concat (rxa::tl,red) when compare rxa rxh = 0 ->
	    (Set.add (Concat (tl,red)) tls,rst)
	  | rx -> (tls, Set.add rx rst)
	in
	let tails,rest = Set.fold put_in_group rxs (Set.empty, Set.empty) in
	let ftails = factor_rxs tails in
	let merged =
	  if Set.cardinal ftails = 1 then
	    match Set.choose ftails with
		Concat (chars,_) ->
		  Concat (rxh::chars, false)
	      | _ -> assert false
	  else
	    Concat ([rxh;Union ftails],false)
	in
	Set.add merged (factor_rxs rest)
      | rx ->
	let factored_tail = factor_rxs (Set.remove rx rxs) in
	Set.add rx factored_tail

let factor_rx = function
  | Union rxs ->
    let concat,other = Set.partition (function Concat _ -> true | _ -> false) rxs in
    Union (Set.union (factor_rxs concat) other)
  | x -> x
