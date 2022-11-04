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
(*
let rec move_aux (nfa: ('q,'s) nfa_t) (qs: 'q list) (s: 's option) (states_list: 'q list): 'q list =
match nfa.delta with
| []-> []
| h->
match h with
| [] -> []
| ([(loc, trans, dest)] : ('q, 's) transition list) ->
if loc = List.nth qs 0 && trans = s then
List.concat[states_list; [dest]]
else if loc != List.nth qs 0 && trans != s then
states_list
else
states_list
| h::t->
match h with
| ((loc, trans, dest) : ('q, 's) transition) ->
if loc = List.nth qs 0 && trans = s then
List.concat[states_list;[dest]]
(*else if loc != List.nth qs 0 && trans != s then*)
else
let new_nfa = {sigma = nfa.sigma; qs = nfa.qs; q0 = nfa.q0; fs = nfa.fs; delta = t}
in
move_aux new_nfa qs s states_list

(*Start of move function!!*)

let move (nfa: ('q,'s) nfa_t) (qs: 'q list) (s: 's option) : 'q list =
if (List.find (fun s -> s) (nfa.sigma)) = true then
 move_aux nfa qs s []
else []
*)

(*Final version of move*)
let move (nfa: ('q,'s) nfa_t) (qs: 'q list) (s: 's option) : 'q list =
fold_left(fun result h -> match h with (loc, trans, dest) ->
	      if (mem dest result) = false && mem loc qs && trans = s then
	      dest::result else result) [] nfa.delta 
(*How can I recursively call upon the rest of the elements in delta list? Fold left or Rec helper function*)

(*
let rec closure_aux  (nfa: ('q,'s) nfa_t) (qs: 'q list) (result: 'q list) : 'q list = 
match nfa.delta with
| [] -> result
| h::t -> (
        match h with
        | ((loc, trans, dest) : ('q, 's) transition)->
          let new_nfa = {sigma = nfa.sigma; qs = nfa.qs; q0 = nfa.q0; fs = nfa.fs; delta = t}
          in
          if trans = None && mem loc qs && (mem loc result) = false && (mem dest result)=false then
           let result = List.concat[result; [loc; dest]] in 
           closure_aux new_nfa qs result
          else if trans = None && mem loc qs && (mem loc result) = true && (mem dest result)=false then
           let result = List.concat[result; [dest]] in
           closure_aux new_nfa qs result
          else closure_aux new_nfa qs result 
)

let e_closure (nfa: ('q,'s) nfa_t) (qs: 'q list) : 'q list =
match nfa.delta with
| [] -> []
| h::t -> (
     match h with
     | ((loc, trans, dest) : ('q, 's) transition)->
       let new_nfa = {sigma = nfa.sigma; qs = nfa.qs; q0 = nfa.q0; fs = nfa.fs; delta = t}
       in
       if trans = None && (List.nth qs 0) = loc then
         closure_aux new_nfa qs [loc;dest]
       else if trans = None && (List.nth qs 0) != loc then
        closure_aux new_nfa qs qs
       else if trans != None then
        let result = List.concat[[];qs]
        in
        closure_aux new_nfa qs result
       else []
       )*)

(*Final version of e_closure and helper functions*)
let unique_list lst = List.fold_left (fun x y -> if List.mem y x then x else y::x) [] lst 

let rec e_closure_aux delta new_delta q lst =
match new_delta with
| [] -> [q]
| h::t -> match h with
          | (loc, trans, dest) -> if loc = q && trans = None && (List.mem dest lst) = false then 
             (e_closure_aux delta t q (dest::lst)) @ (e_closure_aux delta delta dest (dest::lst)) @ [loc]
             else (e_closure_aux delta t q lst)
 

let rec e_closure (nfa: ('q,'s) nfa_t) (qs: 'q list) : 'q list =
 unique_list (List.fold_left ( fun x y -> (e_closure_aux nfa.delta nfa.delta y []) @ x) [] qs)

(*Helper Functions for accept*)
let trans_lookup (delta : ('q, 's) transition list) (curr_state : 'q) (character: 's) =
List.filter (fun (s, co, _) ->
		 let valid = match co with
		 | Some c -> c = character 
                 | None -> true
		 in
		 s = curr_state && valid) delta

let check_characters (s: string) : char list =
 if List.length (explode s) = 0 then
   [' ']
 else explode s
(*
let rec accept_aux (nfa: ('q,'s) nfa_t) (curr_state : 'q) (characters: char list) = 
  match characters with
  | [] -> List.mem curr_state nfa.fs
  | h::t -> 			    
    let valid_trans = trans_lookup nfa.delta curr_state h in
    let results = List.map (fun x -> let (_,_,next_state) = x in accept_aux nfa next_state t) valid_trans in
    if List.length results = 0 then 
      false
    else 
      List.fold_left (fun x y -> x || y) false results   
     

let accept (nfa: ('q, char) nfa_t) (s: string) : bool =
  let characters = check_characters s in
  let curr_state = nfa.q0 in
  match characters with 
  | [] -> false
  | h::t -> 
    let valid_trans = trans_lookup nfa.delta curr_state h in
    let results = List.map (fun x -> let (_,_,next_state) = x in accept_aux nfa next_state t) valid_trans in
    if List.length results = 0 then
     false
    else
List.fold_left (fun x y -> x || y) false results
*)

(*Final version of accept is below nfa_to_dfa; nfa_to_dfa allows for accpet to work fully*)

(*******************************)
(* Part 2: Subset Construction *)
(*******************************)

let rec new_states_helper sigma qs nfa =
match sigma with
  |[] -> [] 
  |h :: t -> (e_closure nfa (move nfa qs (Some h))) :: (new_states_helper t qs nfa)

let rec new_finals_helper states qs =
match states with
  |[] -> [] 
  |h :: t -> if (elem h qs) then [qs] else (new_finals_helper t qs)

let new_states (nfa: ('q,'s) nfa_t) (qs: 'q list) : 'q list list = 
(new_states_helper nfa.sigma qs nfa) 

let new_trans (nfa: ('q,'s) nfa_t) (qs: 'q list) : ('q list, 's) transition list =
let rec new_trans_aux acc l =
  match l with
  | [] -> acc
  | h::t -> new_trans_aux(acc@[((qs, Some h, ((e_closure nfa ((move nfa qs (Some h)))))))]) t
  in new_trans_aux [] (nfa.sigma)

let new_finals (nfa: ('q,'s) nfa_t) (qs: 'q list) : 'q list list =
(new_finals_helper nfa.fs qs)

let rec nfa_to_dfa_step (nfa: ('q,'s) nfa_t) (dfa: ('q list, 's) nfa_t)
    (work: 'q list list) : ('q list, 's) nfa_t =
    match work with
    |[] -> dfa 
    |h :: t -> if (h != []) then (let dfa_return =
	      {
    	        sigma = dfa.sigma ;
		qs = (insert h dfa.qs) ;
		q0 =  dfa.q0 ;
		fs = (union (new_finals nfa h)  dfa.fs);
		delta = (union (new_trans nfa h)  dfa.delta)
	       } in
	         let  x = minus (union (new_states nfa h) (t)) dfa_return.qs in (nfa_to_dfa_step nfa dfa_return x))
                 else (nfa_to_dfa_step nfa dfa t)

let nfa_to_dfa (nfa: ('q,'s) nfa_t) : ('q list, 's) nfa_t =
 let start = [(e_closure nfa [nfa.q0])] in
 let dfa = {
            sigma = nfa.sigma ;
            qs = [(e_closure nfa [nfa.q0])] ;
            q0 = (e_closure nfa [nfa.q0]) ;
            fs = [] ;
            delta = []
           } in (nfa_to_dfa_step nfa dfa start)

(*Final version of accept*)
let rec accept_helper nfa curr str_arr =
if (curr = []) then [] else
match str_arr with
  |[] -> curr 
  |h :: t -> (accept_helper nfa (move nfa curr (Some h)) t)

let accept (nfa: ('q,char) nfa_t) (s: string) : bool =
let dfa = (nfa_to_dfa nfa) in
match (accept_helper dfa [dfa.q0] (explode s)) with
    |[] -> false
    |h :: t -> (elem h dfa.fs)
