open Batteries

(** This module parses semi-Perl compatable Regular Expressions
  *
  * It is part of the NetSifter project
  *
  *)

type char_token = [
                  | `Char of int
		  | `Escape of char list
		  ]

type stream_token =
  [ char_token
  | `Class of string
  | `Substart
  | `Substop
  | `Caret (* ^ *)
  | `Any (* . *)
  | `Alternate (* | *)
  | `Repeat of int * int option (* {3,} {2,4} {8} *)
  ]

type class_token =
    [ char_token (* `Char of int, `Escape of char list *)
    | `Range of int * int
    | `Class of string
    ]

(** RegEx type *)
type ('a,'b) t =
  | Union of ('a,'b) t list
  | Concat of ('a,'b) t list
  | Kleene of ('a,'b) t
  | Value of 'a
  | Accept of 'b

let epsilon = Union []

let catch_escape = function
  | '\\'::'x'::h1::h2::t ->
      Some (`Char (int_of_string (Printf.sprintf "0x%c%c" h1 h2)), t)
  | '\\'::'x'::'{'::t ->
      let rec loop acc = function
	  '}' :: t ->
	    Some (`Char (int_of_string (String.implode (List.rev acc))), t)
	| c :: t -> loop (c::acc) t
	| [] -> failwith "End reached looking for }"
      in
      loop ['x';'0'] t
  | '\\'::'c'::x::t ->
      let to_control_char c =
	let upper_code = Char.uppercase c |> Char.code in
	(upper_code lxor 0x60) in
      Some (`Char (to_control_char x), t)
  | '\\'::'n'::t -> Some (`Char (Char.code '\n'),t)
  | '\\'::'r'::t -> Some (`Char (Char.code '\r'),t)
  | '\\'::'t'::t -> Some (`Char (Char.code '\t'),t)
  | '\\'::'a'::t -> Some (`Char 0x07,t) (* bell *)
  | '\\'::'e'::t -> Some (`Char 0x1b,t) (* escape *)
  | '\\'::'f'::t -> Some (`Char 0x0c,t) (* form feed *)
  | '\\'::'v'::t -> Some (`Char 0x0b,t) (* vertical tab *)
  | '\\'::x::t -> Some (`Escape [x], t)
  | c::t -> Some (`Char (Char.code c), t)
  | [] -> None

let catch_class char_list =
  let acc = Buffer.create 15 in
  let rec aux count = function
    | '['::':'::'a'::'l'::'n'::'u'::'m'::':'::']'::b ->
	Buffer.add_string acc "a-zA-Z0-9"; aux count b
    | '['::':'::'s'::'p'::'a'::'c'::'e'::':'::']'::b ->
	Buffer.add_string acc " \\t\\r\\n\\v\\f"; aux count b
(* TODO: COMPLETE LIST OF POSIX BRACKET EXPRESSIONS FROM HERE:
   http://www.regular-expressions.info/posixbrackets.html *)
    | '['::b ->  (Buffer.add_char acc '[') ; aux (count+1) b
    | ']'::b when count == 0 -> `Class (Buffer.contents acc), b
    | ']'::b when count != 0 ->  (Buffer.add_char acc ']') ; aux (count-1) b
    | a::b -> (Buffer.add_char acc a) ; aux  (count) b
    | [] -> `Class (Buffer.contents acc), []
  in
    aux 0 char_list

let rec get_int acc = function
    ('0'..'9' as d) :: t -> get_int (10*acc + (Char.code d - 0x30)) t
  | t -> acc, t

let catch_range chars =
  let (v0,chars) = get_int 0 chars in
  match chars with
      ',' :: chars ->
	let (v1,chars) = get_int 0 chars in
	( match chars with
	      '}'::chars -> `Repeat (v0,if v1 = 0 then None else Some v1), chars
	    | _ -> failwith "Expecting } for range"
	)

    | '}':: chars -> `Repeat (v0,Some v0), chars
    | _ -> failwith "Expecting } or , for range"

let stream_tokenize str =
  let rec make_token = function
    | [] -> None
    | '\\'::_ as l -> catch_escape l
    | '['::t -> Some ( catch_class t )
    | '(' :: '?' :: ':' :: t | '('::t
	-> Some ( `Substart, t )
    | ')'::t -> Some ( `Substop, t )
    | '^'::t -> Some ( `Caret, t )
    | '.'::t -> Some ( `Any, t )
    | '|'::t -> Some ( `Alternate, t )
    | '?'::t -> Some ( `Repeat (0,Some 1), t )
    | '*'::t -> Some ( `Repeat (0,None), t )
    | '+'::t -> Some ( `Repeat (1,None), t )
    | '{'::t -> Some ( catch_range t )
    | c::t  (* ignores whitespace *)
	when (c == '\n') || (c==' ')
	  || (c=='\r') || (c=='\t') -> make_token t
    | c::t   -> Some ( (`Char (Char.code c)), t )
  in
    Enum.unfold (String.explode str) make_token ;;


let class_tokenize str =
  let token_stream = Enum.unfold (String.explode str) catch_escape |> List.of_enum in
  let rec parse_class = function
    | [] -> None
    | `Char a::`Char 45 (* - *)::`Char b::t ->
      if a > b then parse_class t else Some (`Range (a,b), t)
    | `Char c::t   -> Some ( `Char c, t )
    | `Escape e::t -> Some (`Escape e,t)
  in
    match token_stream with
      | `Char 94 (* ^ *) :: t -> (false, Enum.unfold t parse_class)
      | b -> (true, Enum.unfold b parse_class) ;;

let iset_of_class any set_of_escape str =
  let aux acc = function
    | `Char c -> ISet.add c acc
    | `Range (lo,hi) -> ISet.add_range lo hi acc
    | `Escape x -> ISet.union (set_of_escape x) acc
  in
  let (positive, tokens) = class_tokenize str in
  if positive
  then fold aux ISet.empty tokens
  else ISet.diff any (fold aux ISet.empty tokens)

let rev_compare x y = - (Pervasives.compare x y)

let rec union_elim acc = function
    [] -> List.sort_unique Pervasives.compare acc
  | Union x :: t -> union_elim acc (x@t)
  | h :: t -> union_elim (h::acc) t


let rec concat_elim acc = function
    [] -> List.rev acc
  | Concat x :: t -> concat_elim acc (x@t)
  | h :: t -> concat_elim (h::acc) t


let rec reduce = function
  | Union [x] -> reduce x
  | Union l -> Union (union_elim [] l |> List.map reduce)
  | Concat [] -> epsilon
  | Concat [x] -> reduce x
  | Concat (Kleene a :: Kleene b :: tl) when a=b -> reduce (Concat (Kleene a::tl))
  | Concat l -> Concat (concat_elim [] l |> List.map reduce)
  | Kleene x -> Kleene (reduce x)
  | Value _ as e -> e
  | Accept _ as e -> e


let rec print_regex printv printa ?root oc =
  let self = print_regex printv printa ?root in
    function
  | x when (match root with Some r -> r==x | None -> false) ->
    IO.nwrite oc "ROOT"
  | Union [Concat []; reg] -> self oc reg; IO.write oc '?'
  | Union regl -> List.print ~first:"(" ~sep:"|" ~last:")" self oc regl
  | Concat regl -> List.print ~first:"" ~sep:"" ~last:"" self oc regl
  | Kleene (Concat regl) -> List.print ~first:"(" ~sep:"" ~last:")" self oc regl;  IO.write oc '*'
  | Kleene reg -> self oc reg; IO.write oc '*'
  | Value a -> printv oc a
  | Accept i -> printa oc i

let print_char oc i =
  IO.nwrite oc (Char.escaped (Char.chr i))

let print_range oc lo hi =
  if lo = hi-1 then begin
    print_char oc lo;
    print_char oc hi;
  end else if lo < hi then begin
    print_char oc lo;
    IO.nwrite oc "-";
    print_char oc hi;
  end else
    print_char oc lo
(*  IO.nwrite oc "  "*)

let print_iset oc set =
  match ISet.cardinal set with
      256 -> IO.write oc '.'
    | 1 -> ISet.iter_range (print_range oc) set
    | _ ->
      IO.write oc '[';
      ISet.iter_range (print_range oc) set;
      IO.write oc ']'

let print_iregex oc = print_regex print_iset ~root:(Obj.magic 0) oc

(* Returns a regex that matches any character in the string *)
let iset_of_string str =
  let add_char acc c = ISet.add (Char.code c) acc in
  String.fold_left add_char ISet.empty str

(**  Takes a ascii str and returns a ISet.t  t
     assume that the regex is not anchored unless explicitly anchored *)
let regex_of_ascii_str ~dec str =
  let stream = stream_tokenize str in
  let escape_char_set = function (* TODO: implement more \. escapes *)
    | 'n' -> iset_of_string "\n"
    | 'r' -> iset_of_string "\r"
    | 't' -> iset_of_string "\t"
    | 'a' -> ISet.singleton 0x07 (* bell *)
    | 'e' -> ISet.singleton 0x1b (* escape *)
    | 'f' -> ISet.singleton 0x0c (* form feed *)
    | 'v' -> ISet.singleton 0x0b (* vertical tab *)
    | 'd' -> iset_of_string "0123456789"
    | 's' -> iset_of_string " \t\r\n"
    | x -> iset_of_string (String.of_char x)
  in
  let value_of_escape = function (* TODO: Implement more escape types *)
    | [] -> failwith "End of string after escape"
    | [x] -> escape_char_set x
    | _ -> failwith "Unknown escape sequence"
  in
  let any = ISet.add_range 0 255 ISet.empty in
  let regex_of_class str = Value (iset_of_class any value_of_escape str) in
  let dup_n rx n = Concat (List.make n rx) in
  let rec zero_thru_n rx n =
    assert (n>0);
    if n = 1 then Union [epsilon; rx]
    else Union [epsilon; Concat [rx; zero_thru_n rx (n-1)]] in
  let rec aux acc =
    let mod_head f = match acc with [] -> assert false
      | h :: t -> aux (f h :: t) in
    match Enum.get stream with
      | None -> Concat (List.rev acc)
      | Some (`Char a) ->
	aux ((Value (ISet.singleton a))::acc)
      | Some (`Escape a) ->
	aux (Value (value_of_escape a)::acc)
      | Some (`Class a) ->
	aux ((regex_of_class a)::acc)
      | Some (`Substart) ->
	aux ((aux [] )::acc)
      | Some (`Substop) ->  Concat (List.rev acc)
      | Some (`Caret) -> aux (Value (iset_of_string "^")::acc)
      | Some (`Any) -> aux ((Value any)::acc)
      | Some (`Alternate) -> (* This is tricky *)
	aux [Union [Concat (List.rev acc) ;aux [] ] ]
      | Some (`Repeat (m,None)) -> (* unbounded *)
	mod_head (fun g -> Concat [dup_n g m; Kleene g])
      | Some (`Repeat (0, Some n)) ->
	mod_head (fun g -> zero_thru_n g n)
      | Some (`Repeat (m, Some n)) when n = m ->
	mod_head (fun g -> dup_n g m)
      | Some (`Repeat (m, Some n)) ->
	mod_head (fun g -> Concat [dup_n g m; zero_thru_n g (n-m)])
  in
  let rx =
    match Enum.peek stream with
      | Some (`Caret) ->
	Enum.junk stream;
	reduce (aux [])
      | _ -> reduce (Concat [Kleene (Value any); aux []])
  in
  reduce (Concat [rx; Accept dec])
;;


let match_char iset c = ISet.mem (Char.code c) iset

let regex_match match_val rx lst =
  let rec loop = function
  | Value _, [] -> None
  | Value v, c::t -> if match_val v c then Some t else None
  | Union [], _ -> None
  | Union (h::t), str -> (* does this backtrack properly? *)
      ( match loop (h,str) with
	  None -> loop (Union t, str)
	| Some t -> Some t )
  | Concat [], str -> Some str
  | Concat (h::t), str ->
      ( match loop (h,str) with
	    None -> None
	  | Some str_t -> loop (Concat t, str_t) )
  | Kleene rx, str -> loop (Union [epsilon; Concat [rx; Kleene rx]],str)
  | Accept _, str -> Some str
  in
  loop (rx,lst)

let regex_match_iset rx str =
  match regex_match match_char rx (String.explode str) with
      Some [] -> true
    | Some _ -> false (* partial match *)
    | None -> false

let line_to_regex ?(allow_comments=false) ~anchor (dec,line) =
  if allow_comments && (String.length line < 1 || line.[0] = '#') then None else begin
(*    eprintf "#Regex:  %s\n" line; *)
    let l = if anchor then "^" ^ line else line in
    Some (regex_of_ascii_str ~dec l)
  end

let join_regex e_rx = Union (List.of_enum e_rx)

let rx_of_dec_strings ?(anchor=false) ?allow_comments ?(max_regs=max_int) rxs =
   Enum.filter_map (line_to_regex ~anchor ?allow_comments) rxs
     |> Enum.take max_regs
     |> join_regex
