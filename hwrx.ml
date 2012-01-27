(* This module parses alternate-style regex
   
   At the moment, only * is a metacharacter, and it means .*
   all other characters are literal.
*)

open Batteries
open Pcregex

let any_char = ISet.add_range 0 255 ISet.empty
let dot_star = Kleene (Value any_char)

let is_hex = function '0'..'9' | 'a'..'f' | 'A'..'F' -> true | _ -> false
let twohex_to_char h1 h2 =
  let to_int = function 
    | '0'..'9' as d -> Char.code d - Char.code '0'
    | 'a'..'f' as x -> Char.code x - Char.code 'a' + 10
    | 'A'..'F' as x -> Char.code x - Char.code 'A' + 10
    | _ -> assert false
  in
  to_int h1 * 16 + to_int h2 |> Char.chr
let rec flatten_byte_literals = function
  | [] -> []
  | '|'::t -> proc_byte t
  | x::t -> x::flatten_byte_literals t
and proc_byte = function
  | h1::h2::t when is_hex h1 && is_hex h2 -> twohex_to_char h1 h2 :: proc_byte t
  | '|'::t -> flatten_byte_literals t
  | c::_ -> failwith (Printf.sprintf "Unexpected char: %c" c)
  | [] -> failwith "Final | not found in byte literal"

let regex_of_ascii_str ~dec str =
  let to_rx_token = function
    | '*' -> dot_star
    | '?' -> Value any_char
    | c -> Value (ISet.add (Char.code c) ISet.empty)
  in
  let tokens = String.explode str |> flatten_byte_literals |> List.rev_map to_rx_token in
  Concat (List.rev_append tokens [Accept dec])

let line_to_regex ?(allow_comments=false) ~anchor (dec,line) =
  if allow_comments && (String.length line < 1 || line.[0] = '#') 
  then None 
  else begin
    (*    eprintf "#Regex:  %s\n" line; *)
    let rx = regex_of_ascii_str ~dec line in
    if anchor then 
      Some rx
    else 
      Some (Concat [dot_star;rx])
  end

let rx_of_dec_strings ?(anchor=false) ?allow_comments ?(max_regs=max_int) rxs =
   Enum.filter_map (line_to_regex ~anchor ?allow_comments) rxs
     |> Enum.take max_regs
     |> join_regex
