open Regex

exception Not_implemented


let rec regex2nfa : Regex.t -> Nfa.t 
=fun regex -> 
let nfa1 = (Nfa.create_new_nfa () )in
let is = Nfa.get_initial_state nfa1 in
(match regex with
|Empty -> let (fs,_) = Nfa.create_state nfa1 in (Nfa.add_final_state nfa1 fs)
|Epsilon -> let (fs,_) = Nfa.create_state nfa1 in
            let nfa2 = Nfa.add_final_state nfa1 fs in
            Nfa.add_epsilon_edge nfa2 (is,fs)
|Alpha x -> let (fs,_) = Nfa.create_state nfa1 in
            let nfa2 = Nfa.add_final_state nfa1 fs in
            Nfa.add_edge nfa2 (is, x, fs) 
|OR (r1,r2) -> let nfa_r1 = (regex2nfa r1) in
               let nfa_r2 = (regex2nfa r2) in
               let (fs,_) = Nfa.create_state nfa1 in 
               let nfa2 = (Nfa.add_final_state nfa1 fs) in
               let nfa3 = (Nfa.add_states nfa2 (Nfa.get_states nfa_r1)) in
               let nfa4 = (Nfa.add_states nfa3 (Nfa.get_states nfa_r2)) in
               let (fs_r1,_) = (BatSet.pop (Nfa.get_final_states nfa_r1)) in
               let (fs_r2,_) = (BatSet.pop (Nfa.get_final_states nfa_r2)) in
               let nfa5 = (Nfa.add_edges nfa4 ([], [(is, Nfa.get_initial_state nfa_r1);(is,Nfa.get_initial_state nfa_r2);(fs_r1,fs);(fs_r2,fs)])) in
               let nfa6 = (Nfa.add_edges nfa5 (Nfa.get_edges nfa_r1)) in
               (Nfa.add_edges nfa6 (Nfa.get_edges nfa_r2))
|CONCAT (r1,r2) -> let nfa_r1 = (regex2nfa r1) in  
                   let nfa_r2 = (regex2nfa r2) in  
                   let (fs_r1,_) = (BatSet.pop (Nfa.get_final_states nfa_r1)) in
                   let (fs_r2,_) = (BatSet.pop (Nfa.get_final_states nfa_r2)) in
                   let (fs,_) = Nfa.create_state nfa1 in 
                   let nfa2 = (Nfa.add_final_state nfa1 fs) in
                   let nfa3 = (Nfa.add_states nfa2 (Nfa.get_states nfa_r1)) in
                   let nfa4 = (Nfa.add_states nfa3 (Nfa.get_states nfa_r2)) in
                   let nfa5 = (Nfa.add_edges nfa4 ([], [(is,Nfa.get_initial_state nfa_r1);(fs_r1,Nfa.get_initial_state nfa_r2);(fs_r2,fs)])) in
                   let nfa6 = (Nfa.add_edges nfa5 (Nfa.get_edges nfa_r1)) in
                  (Nfa.add_edges nfa6 (Nfa.get_edges nfa_r2))
|STAR r -> let nfa_r = (regex2nfa r) in 
           let (fs,_) = Nfa.create_state nfa1 in 
           let nfa2 = (Nfa.add_final_state nfa1 fs) in
           let nfa3 = (Nfa.add_states nfa2 (Nfa.get_states nfa_r)) in
           let (fs_r,_) = (BatSet.pop (Nfa.get_final_states nfa_r)) in
           let nfa4 = (Nfa.add_edges nfa3 ([], [(is, Nfa.get_initial_state nfa_r);(fs_r,Nfa.get_initial_state nfa_r); (fs_r,fs);(is,fs)])) in
           (Nfa.add_edges nfa4 (Nfa.get_edges nfa_r))
)                          



(*e-closure*)
let rec e_closure_r : Nfa.t -> Nfa.states ->Nfa.states -> Nfa.states
= fun nfa states a-> 
if states=BatSet.empty then a 
else
     ( let (s,states') = BatSet.pop states in
      let next =  (Nfa.get_next_state_epsilon nfa s) in
      let a' = BatSet.union (BatSet.add s next) a in
      (e_closure_r nfa (BatSet.union states' next)  a') )

let e_closure nfa states = (e_closure_r nfa states BatSet.empty)

(*union of delta(state,alphabet)*)
let rec reachable : Nfa.t -> Nfa.states -> Regex.alphabet -> Nfa.states -> Nfa.states
=fun nfa q c a ->
if q=BatSet.empty then a
else (
    let (s,states') = BatSet.pop q in
    let next = (Nfa.get_next_state nfa s c) in
    let a' = BatSet.union next a in
    (reachable nfa states' c a')
)

(*one step of worklist algo*)
let update : Nfa.t -> Dfa.t -> Dfa.states -> Dfa.state list -> Dfa.state -> Regex.alphabet -> (Dfa.t * Dfa.states * Dfa.state list)
= fun nfa dfa d w q a ->
let (fs,_) = BatSet.pop (Nfa.get_final_states nfa) in
let new_t =  e_closure nfa (reachable nfa q a BatSet.empty) in
      (let w' = w@[new_t] in
      let d' = (BatSet.add new_t d) in
      let dfa1 = (if (BatSet.mem fs new_t) then (Dfa.add_final_state dfa new_t)
                 else (Dfa.add_state dfa new_t)) in
      let dfa2 = Dfa.add_edge dfa1 (q, a ,new_t) in   
      (if(BatSet.mem new_t d) then (dfa2,d,w) else (dfa2,d',w')))       


(*algorithm of nfa2dfa*)
let rec worklist : Nfa.t -> Dfa.t -> Dfa.states -> Dfa.state list -> Dfa.t
= fun nfa dfa d w -> 
(match w with
|[]-> dfa
|hd::tl -> let (dfa1,d1,w1) = (update nfa dfa d tl hd Regex.A) in
           let (dfa2,d2,w2) = (update nfa dfa1 d1 w1 hd Regex.B) in
           (worklist nfa dfa2 d2 w2)
)


let nfa2dfa : Nfa.t -> Dfa.t
=fun nfa -> 
let d0 = e_closure nfa (BatSet.singleton (Nfa.get_initial_state nfa)) in
let dfa1 = Dfa.create_new_dfa d0 in
let (fs,_) = BatSet.pop (Nfa.get_final_states nfa) in
let dfa2 = if (BatSet.mem fs d0) then (Dfa.add_final_state dfa1 d0) else dfa1 in
(worklist nfa dfa2 (BatSet.singleton d0) [d0])


 
(* Do not modify this function *)
let regex2dfa : Regex.t -> Dfa.t
=fun regex -> 
  let nfa = regex2nfa regex in
  let dfa = nfa2dfa nfa in
    dfa

(*recursive step of checking delta(state,input)*)
let rec check : Dfa.t -> alphabet list -> Dfa.state -> bool
=fun dfa str cs ->
match str with
|[] -> (Dfa.is_final_state dfa cs)
|hd::tl -> (check dfa tl (Dfa.get_next_state dfa cs hd))


let run_dfa : Dfa.t -> alphabet list -> bool
=fun dfa str -> 
let is = Dfa.get_initial_state dfa in
(check dfa str is)
