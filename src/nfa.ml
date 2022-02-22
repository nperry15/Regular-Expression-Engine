open List
open Sets

(*********)
(* Types *)
(*********)

type ('q, 's) transition = 'q * 's option * 'q

type ('q, 's) nfa_t = {
  sigma: 's list;
  qs: 'q list;
  q0: 'q;
  fs: 'q list;
  delta: ('q, 's) transition list;
}

(***********)
(* Utility *)
(***********)

(* explode converts a string to a character list *)
let explode (s: string) : char list =
  let rec exp i l =
    if i < 0 then l else exp (i - 1) (s.[i] :: l)
  in
  exp (String.length s - 1) []

(****************)
(* Part 1: NFAs *)
(****************)


let move (nfa: ('q,'s) nfa_t) (qs: 'q list) (s: 's option) : 'q list =
  match nfa with {sigma; qs = ql; q0; fs; delta} ->
  List.fold_left (fun acc trans -> 
    (match trans with | (home, tran, dest) -> 
      if List.mem home qs && tran = s && not (List.mem dest acc) then
        dest::acc 
      else 
        acc)) [] delta

(*
let move (nfa: ('q,'s) nfa_t) (qs: 'q list) (s: 's option) : 'q list =
let out = [] in
  let l = List.nth qs 0 in 
  let trans = List.nth nfa.delta 0 in
  if (match trans with | (a,b,c) -> a) = l then
    if (match trans with | (a,b,c) -> b) = s then 
      out@[(match trans with | (a,b,c) -> c)] 
    else 
      out@[]
  else 
    out@[]
*)

let rec e_helper nfa e qs_h =
  match nfa with {sigma; qs = qx; q0; fs; delta} ->
      if not (e = qs_h) then 
        e_helper nfa qs_h (List.fold_left (fun acc trans -> match trans with (home, tran, dest) ->
        if tran = None && not (List.mem dest acc) && List.mem home qs_h then
          [dest]@acc
        else
          acc)
        qs_h delta)
      else 
        qs_h

let e_closure (nfa: ('q,'s) nfa_t) (qs: 'q list) : 'q list =
  List.fold_left (fun acc closure -> if List.mem closure acc then acc else closure::acc) []
    (e_helper nfa [] qs)

let get_chars d_q0 d_fs fold_func s = 
  let chars = explode s in
    let final = List.fold_left fold_func [d_q0] chars in
    match final with
    | [] -> false
    | (x::xs) -> List.mem x d_fs

let new_states (nfa: ('q,'s) nfa_t) (qs: 'q list) : 'q list list =
  match nfa with {sigma; qs = qx; q0; fs; delta} ->
  List.fold_left (fun acc char -> [e_closure nfa (move nfa qs (Some char))]@acc) [] sigma

let new_trans (nfa: ('q,'s) nfa_t) (qs: 'q list) : ('q list, 's) transition list =
  match nfa with {sigma; qs = qx; q0; fs; delta} ->
  List.fold_left (fun acc char -> [(qs, Some char, e_closure nfa (move nfa qs (Some char)))]@acc) [] sigma

let new_finals (nfa: ('q,'s) nfa_t) (qs: 'q list) : 'q list list =
  match nfa with {sigma; qs = qx; q0; fs; delta} ->
  List.fold_left (fun acc char -> if List.mem char fs then [qs]@acc else acc) [] qs

let rec nfa_to_dfa_step (nfa: ('q,'s) nfa_t) (dfa: ('q list, 's) nfa_t)
    (work: 'q list list) : ('q list, 's) nfa_t =
let not_located_func = (fun acc del -> if not (List.mem del acc) then del::acc else acc) in
  match dfa with {sigma = d_sigma; qs = d_qs; q0 = d_q0; fs = d_fs; delta = d_delta} ->
  let del_func = (fun acc del -> if List.mem del d_qs then acc else del::acc) in
  match nfa with {sigma = n_sigma; qs = n_qs; q0 = n_q0; fs = n_fs; delta = n_delta} ->
  let acc_list_func = (fun acc hold -> acc@(new_finals nfa hold)) in
  match work with
  | [] -> {sigma = d_sigma; qs = d_qs; q0 = d_q0; 
          fs = List.fold_left acc_list_func [] d_qs; 
          delta = List.fold_left not_located_func [] d_delta}
  | (x::xs) -> nfa_to_dfa_step nfa
    {sigma = d_sigma; 
    qs = List.fold_left not_located_func d_qs (new_states nfa x); 
    q0 = d_q0; fs = d_fs; 
    delta = (new_trans nfa x)@d_delta} 
    (xs@(List.fold_left del_func [] (new_states nfa x)))

let nfa_to_dfa (nfa: ('q,'s) nfa_t) : ('q list, 's) nfa_t =
  match nfa with {sigma; qs = qx; q0; fs; delta} ->
  nfa_to_dfa_step nfa {sigma = sigma; qs = [e_closure nfa [q0]]; 
    q0 = e_closure nfa [q0]; fs = []; delta = []} [e_closure nfa [q0]]

let accept (nfa: ('q,char) nfa_t) (s: string) : bool =
  let dfa = nfa_to_dfa nfa in
  let fold_func = (fun acc char -> move dfa acc (Some char)) in
    match dfa with {sigma; qs = qx; q0; fs; delta} -> get_chars q0 fs fold_func s

(*******************************)
(* Part 2: Subset Construction *)
(*******************************)


