open Regex
open Hw1


let testcases : (Regex.t * alphabet list) list = 
  [ 
    (CONCAT (STAR (CONCAT (Alpha A, CONCAT (Alpha B, Alpha A))), STAR (CONCAT (Alpha B, Alpha B))), [A;B;A;A;B;A;B;B;B]);
    (CONCAT (STAR (OR (Alpha A, Alpha B)), CONCAT (Alpha B, Alpha A)), [A;A;B;B;B;A;B]);
    (OR (STAR (CONCAT (Alpha B, Alpha A)), STAR (CONCAT (Alpha A, Alpha B))), [A;B;A;B;A]);
    (STAR (OR (CONCAT (Alpha A,Alpha B), Alpha B)), [B;B;B;B;A;B]);
    (CONCAT (OR (Alpha B, Epsilon), CONCAT (STAR (CONCAT (Alpha A, CONCAT (Alpha A, Alpha A))), Alpha B)), [B;A;A;A;A;A;A;B]);
    (CONCAT (STAR (CONCAT (Alpha B, Epsilon)), STAR (CONCAT (Epsilon, Alpha A))), [B;B;B;A;A]);
    (STAR (OR (STAR (CONCAT (Alpha A, CONCAT (Alpha B, Epsilon))), STAR (CONCAT (Alpha B, Alpha B)))), [A;B;A;B;B;B]);
    (OR (STAR (CONCAT (Epsilon, Alpha A)), Alpha B), [A;B]);
    (STAR (OR (CONCAT(Alpha A, Alpha A), CONCAT (CONCAT (Epsilon, Alpha B), CONCAT (Alpha A, Alpha B)))), []);
    (CONCAT  (CONCAT  (STAR  (OR  (Alpha  B,  Epsilon)),  STAR  (OR  (Epsilon,  Alpha  A))),  Epsilon), [B;A;B]);
    (OR (CONCAT (STAR (Alpha B), Empty), CONCAT (STAR (CONCAT (Alpha A, Alpha B)), STAR (CONCAT (Alpha B, Alpha A)))), [A;B;A;B;B;A;B;A;A]);
    (OR (CONCAT (STAR (Alpha B), Empty), CONCAT (STAR (CONCAT (Alpha A, Alpha B)), STAR (CONCAT (Alpha B, Alpha A)))), [A;B;A;B;B;A;B;A;A;B]);
    (OR (CONCAT (STAR (Alpha B), Empty), CONCAT (STAR (CONCAT (Alpha A, Alpha B)), STAR (CONCAT (Alpha B, Alpha A)))), [A;B;A;B;B;A;B;A]);
    (CONCAT (OR (CONCAT (CONCAT (Alpha A, Alpha A), STAR (CONCAT (Alpha A, Alpha B))), OR (STAR (CONCAT (OR (Epsilon, CONCAT (Alpha B, Epsilon)), OR(Epsilon, CONCAT (Alpha B, Epsilon)))), STAR (CONCAT (Alpha B, Alpha A)))), OR (CONCAT (STAR (Alpha A), Alpha B), CONCAT (STAR (Alpha B), Alpha A))), [A;A;B;A;A;A;A;A;A;A;A;A;A;A]);
    (CONCAT (OR (CONCAT (CONCAT (Alpha A, Alpha A), STAR (CONCAT (Alpha A, Alpha B))), OR (STAR (CONCAT (OR (Epsilon, CONCAT (Alpha B, Epsilon)), OR(Epsilon, CONCAT (Alpha B, Epsilon)))), STAR (CONCAT (Alpha B, Alpha A)))), OR (CONCAT (STAR (Alpha A), Alpha B), CONCAT (STAR(Alpha B), Alpha A))), [B;B;A;A;A;A;A;A;A;A;A;A;B;A]);
    (CONCAT (OR (CONCAT (CONCAT (Alpha A, Alpha A), STAR (CONCAT (Alpha A, Alpha B))), OR (STAR (CONCAT (OR (Epsilon, CONCAT (Alpha B, Epsilon)), OR(Epsilon, CONCAT (Alpha B, Epsilon)))), STAR (CONCAT (Alpha B, Alpha A)))), OR (CONCAT (STAR (Alpha A), Alpha B), CONCAT (STAR (Alpha B), Alpha A))), [B;B;A;A;A;A;A;A;A;A;A;A;B]);
    (CONCAT (OR (CONCAT (CONCAT (Alpha A, Alpha A), STAR (CONCAT (Alpha A, Alpha B))), OR (STAR (CONCAT (OR (Epsilon, CONCAT (Alpha B, Epsilon)), OR(Epsilon, CONCAT (Alpha B, Epsilon)))), STAR (CONCAT (Alpha B, Alpha A)))), OR (CONCAT (STAR (Alpha A), Alpha B), CONCAT (STAR (Alpha B), Alpha A))), [A;A;A;B;A;A;A;A;A;A;A;A;A;A;A;B]);
    (OR (CONCAT (CONCAT (Alpha A, CONCAT (Alpha B, Alpha A)), CONCAT (CONCAT (Alpha A, Alpha A), Alpha B)), CONCAT (CONCAT (CONCAT (Alpha A, Alpha B), OR (STAR (CONCAT (Alpha A, Epsilon)), STAR (CONCAT (Alpha B, Empty)))), STAR (CONCAT (Alpha A, Alpha B)))), [A;B;A;A;A;B]);
    (OR (CONCAT (CONCAT (Alpha A, CONCAT (Alpha B, Alpha A)), CONCAT (CONCAT (Alpha A, Alpha A), Alpha B)), CONCAT (CONCAT (CONCAT (Alpha A, Alpha B), OR (STAR (CONCAT (Alpha A, Epsilon)), STAR (CONCAT (Alpha B, Empty)))), STAR (CONCAT (Alpha A, Alpha B)))), [A;B;A;A;A;B;A;B]);
    (OR (CONCAT (CONCAT (Alpha A, CONCAT (Alpha B, Alpha A)), CONCAT (CONCAT (Alpha A, Alpha A), Alpha B)), CONCAT (CONCAT (CONCAT (Alpha A, Alpha B), OR (STAR (CONCAT (Alpha A, Epsilon)), STAR (CONCAT (Alpha B, Empty)))), STAR (CONCAT (Alpha A, Alpha B)))), [A;B;A;A;A;B;A]);
    (STAR (OR (CONCAT (Alpha A, CONCAT (Empty, OR (Alpha A, Epsilon))), CONCAT (OR (Alpha B, Epsilon), CONCAT (Alpha A, CONCAT (Alpha A, Alpha A))))), [A;A;A;B;A;A;]);
    (STAR (OR (CONCAT (Alpha A, CONCAT (Empty, OR (Alpha A, Epsilon))), CONCAT (OR (Alpha B, Epsilon), CONCAT (Alpha A, CONCAT (Alpha A, Alpha A))))), [A;A;A;A;A;A;]);
    (STAR (OR (CONCAT (Alpha A, CONCAT (Empty, OR (Alpha A, Epsilon))), CONCAT (OR (Alpha B, Epsilon), CONCAT (Alpha A, CONCAT (Alpha A, Alpha A))))), [A;A;A;A;A;A;A;]);
    (STAR (OR (CONCAT (Alpha A, CONCAT (Empty, OR (Alpha A, Epsilon))), CONCAT (OR (Alpha B, Epsilon), CONCAT (Alpha A, CONCAT (Alpha A, Alpha A))))), [B;A;A;A;B;A;A;A;]);
    (STAR (OR (CONCAT (Alpha A, CONCAT (Empty, OR (Alpha A, Epsilon))), CONCAT (OR (Alpha B, Epsilon), CONCAT (Alpha A, CONCAT (Alpha A, Alpha A))))), [B;A;A;A;A;A;A;A;])
   
  ]



let match_regex : Regex.t -> alphabet list -> bool
=fun regex input -> Hw1.run_dfa (Hw1.regex2dfa regex) input

(* run testcases *)
let _ = 
  List.iter (fun (regex, str) -> 
    prerr_endline (string_of_bool (match_regex regex str)) 
  ) testcases




(* regex2nfa test///////////////////////////
let nfa_printer = 
  List.iter (fun (regex, _) ->Nfa.print (Hw1.regex2nfa regex)) testcases
*)


(*e-closure test///////////////////////////
let string_of_set set =
  "{ " ^ (BatSet.fold (fun s str -> str ^ string_of_int s ^ ", ") set "") ^ " }"


let e_closure_printer : Nfa.t -> Nfa.states -> unit
= fun nfa s->
  let e = (Hw1.e_closure nfa s) in
  prerr_endline ("e_closure: " ^ string_of_set e)

let reg =   (CONCAT (CONCAT (STAR (CONCAT (Alpha A, Alpha A)), STAR (CONCAT (Alpha B, Alpha B))), Alpha B))
let nfa = (regex2nfa reg) 
let states = BatSet.singleton (Nfa.get_initial_state nfa) ;;
e_closure_printer nfa states;;
Nfa.print nfa;;
*)


(* nfa2dfa test///////////////////////////
let dfa_printer = 
  List.iter (fun (regex, _) ->Dfa.print (Hw1.nfa2dfa (Hw1.regex2nfa regex))) testcases  
*)
 


(* let reg = STAR (OR (STAR (CONCAT (Alpha A, CONCAT (Alpha B, Epsilon))), STAR (CONCAT (Alpha B, Alpha B))))
let nfa = Nfa.print( Hw1.regex2nfa reg )
let _ = print_endline "nfa end"
let dfa = Dfa.print (Hw1.regex2dfa reg )  *)
