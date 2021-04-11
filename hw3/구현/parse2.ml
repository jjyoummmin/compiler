type symbol = T of string | N of string | Epsilon | End 
type production = (symbol * symbol list) list
type cfg = symbol list * symbol list * symbol * production
type first_set = (symbol, symbol BatSet.t) BatMap.t
type follow_set = (symbol, symbol BatSet.t) BatMap.t
type dependency = (symbol , symbol BatSet.t) BatMap.t
type item_symbol = S of symbol | Dot
type item = (symbol * item_symbol list)
type state = (item BatSet.t ) 
type edge = state * symbol * state
type automaton = (state BatSet.t * edge BatSet.t)
type action = Shift of state | Goto of state | Acc | Reduce of (symbol * symbol list)
type table = ((state * symbol) ,action) BatMap.t

(* ==============(0) need follow-set of hw2 to fill SLR parse table (reduce)============== *)
(* /////printer//////// *)
(* symbol -> string *)
let string_of_symbol s = 
match s with
|T x -> x
|N x -> x
|Epsilon -> "epsilon"
|End -> "$"

let string_of_item_symbol is = 
match is with
|Dot -> "."
|S (T x )-> x
|S (N x) -> x
|S (Epsilon) -> "epsilon"
|S (End) -> "$"

(* symbol BatSet.t -> string *)
let string_of_set set =
  "{ " ^ (BatSet.fold (fun s str -> str ^ string_of_symbol s ^ ", ") set "") ^ " }"


let string_of_item (s,l) = 
   (string_of_symbol s) ^ " -> " ^ (List.fold_left (fun a x -> a ^ (string_of_item_symbol x)) "" l)

(* printer for first/follow set *)
let set_printer set = 
    BatMap.iter (fun s symbols -> 
      prerr_endline (string_of_symbol s ^ " -> " ^ string_of_set symbols  )
    ) set


(* printer for state (set of items) *)
let state_printer state = 
    let _ = print_endline "---state---" in
    BatSet.iter (fun item -> print_endline (string_of_item item)) state


(* /////first set////// *)
(* find first set for terminal *)
let rec first_of_t : symbol list -> first_set -> first_set
= fun t a-> 
match t with 
|[]-> a
|hd::tl -> first_of_t tl (BatMap.add hd (BatSet.singleton hd) a)

(* updating set with new element *)
let update_set
=fun set s1 s2 ->
  let old = try BatMap.find s1 set with _ -> BatSet.empty in
  BatMap.add s1 (BatSet.add s2 old) set

let union_set
=fun set s1 s2 ->
  let old = try BatMap.find s1 set with _ -> BatSet.empty in
  BatMap.add s1 (BatSet.union s2 old) set  

(* decide add to worklist or not *)
(* if symbol x is still left as a head of production rule in worklist then not completed *)
let rec find_nonterm
=fun s l ->
match l with
|[] -> false
|(x,y)::tl -> (if s=x then true else (find_nonterm s tl))

(* worklist algorithm for function "first" *)
let rec worklist_first : production -> first_set -> (int ref) -> first_set
=fun w a cnt->
let _ = cnt := !cnt + 1 in
if w = [] then a 
else let (s,l) = List.hd w in
     let tl_of_w = List.tl w in
(
if l=[] then (worklist_first (tl_of_w) (update_set a s Epsilon) cnt)
else let hd = List.hd l in
     let tl_of_l = List.tl l in
(match hd with
|(T x) -> (worklist_first (tl_of_w) (update_set a s (T x)) cnt)
|(N x) -> if ((find_nonterm (N x) tl_of_w) && (!cnt < 300)) then (worklist_first (tl_of_w@[(s,l)]) a cnt)
          else let first_x = try BatMap.find (N x) a with _ -> BatSet.empty in
            (if (BatSet.mem Epsilon first_x)then (worklist_first (tl_of_w@[(s,tl_of_l)]) (union_set a s (BatSet.remove Epsilon first_x)) cnt)
             else worklist_first (tl_of_w) (union_set a s (first_x)) cnt 
            ) 
|Epsilon|End -> raise (Failure "Epsilon / End not implemented")                   
)  
)                 
                   

(* final first set function *)
let first :cfg -> first_set
=fun (n,t,s,p) -> 
let set1 = first_of_t t BatMap.empty in
let cnt = ref 0 in
(worklist_first p set1 cnt)


(* /////follow set////// *)

(* return tl list following target symbol x *)
let rec split_list :symbol -> symbol list -> symbol list
=fun x l ->
match l with
|[]->[]
|hd::tl -> (if x=hd then tl else (split_list x tl))


let rec check_one_pr : first_set ->  (symbol * symbol list) -> symbol  -> follow_set -> dependency ->  (follow_set * dependency)
=fun fs (s,l) x a d->
let after_x_string = (split_list x l) in 
(if (after_x_string = []) then (if s = x then (a,d) else let dep_x = (try BatMap.find x d with _ -> BatSet.empty) in 
                                                         let dep_x_s = BatSet.add s dep_x in
                                                         (a,(BatMap.add x dep_x_s d) ))                  

else (let next_symbol = (List.hd after_x_string) in
      let first_ns = (try BatMap.find next_symbol fs with _ -> BatSet.empty) in
     if(BatSet.mem Epsilon first_ns) then 
          let new_a = (union_set a x (BatSet.remove Epsilon first_ns)) 
          in (check_one_pr fs (s,x::(List.tl after_x_string)) x (new_a) d) 
     else let new_a = (union_set a x (first_ns)) in 
          (new_a, d)     
      )                   
)

(* check related production rule of one target symbol x *)
let rec check_pr : first_set -> production -> symbol -> follow_set  -> dependency -> (follow_set * dependency)
=fun fs pr x a d ->
match pr with
|[] -> (a,d)
|hd::tl ->( let (new_a, new_d) = (check_one_pr fs hd x a d) in
            let (s,l) = hd in
            let after_x_string = (split_list x l) in
            (if (List.mem x after_x_string) then 
            let x_again = x::(split_list x after_x_string) in
            (check_pr fs (tl@[(s,x_again)]) x new_a new_d) else
            (check_pr fs  tl x new_a new_d)) )


(* hd-> target symbol. want to find follow(hd) *)
let rec worklist_follow : first_set -> production ->  symbol BatSet.t -> follow_set -> dependency -> (follow_set * dependency)
=fun fs p w a d -> 
if (w=BatSet.empty) then (a,d)
else let (hd,tl) = BatSet.pop w in
     let pr = (List.fold_left (fun x (s,l) -> if (List.mem hd l) then x@[(s,l)] else x) [] p) in
           if pr = [] then (worklist_follow fs p tl a) d
           else let (new_a, new_d) = (check_pr fs pr hd a d) in 
                (worklist_follow fs p tl new_a new_d)
      



(* make first follow_set  *)
let rec fill : follow_set -> symbol list -> follow_set
=fun set n ->
match n with
|[] -> set
|hd::tl -> (fill (BatMap.add hd (BatSet.empty) set) tl)                                



let rec final_stage : follow_set -> dependency -> int ref -> follow_set
=fun a d cnt->
if (!cnt > 100) then a
else let _ = cnt := !cnt + 1 in 
     let new_a = ( BatMap.foldi (fun key v a ->
     if (v = BatSet.empty) then a
     else (BatSet.fold (fun x a -> let follow_x = (try BatMap.find x a with _ -> BatSet.empty) in
                                  let new_a = (union_set a key follow_x) in new_a
                      ) v a )                       
     ) d a ) in
     (final_stage new_a d cnt )     





(* final follow set function *)
let follow : cfg -> follow_set 
= fun cfg ->
let (n,t,s,p) = cfg in
let fs = (first cfg) in
let set1 = (fill BatMap.empty n) in
let set2 = (update_set set1 s End) in
let w = List.fold_left (fun a x -> BatSet.add x a) BatSet.empty n in
let d = List.fold_left (fun a x-> BatMap.add x BatSet.empty a) BatMap.empty n in
let (set3, dependency) = (worklist_follow fs p w set2 d) in
let cnt = ref 0 in
(final_stage set3 dependency cnt)


(* ==================(1) make dfa====================== *)
(* //////closure//////*)

(* find symbol tht comes after dot *)
let rec after_dot_symbol : item_symbol list -> item_symbol
=fun l ->
match l with
|[] -> raise (Failure "no dot in item body")
|hd::tl -> if (hd=Dot) then (try (List.hd tl) with _ ->S Epsilon)
           else (after_dot_symbol tl)


(* change production rule body to item body *)
let rec make_item : production -> symbol -> state -> state
=fun p x items ->
match p with
|[] -> items
|(s,l)::tl -> if (s=x) then let item_body = List.fold_left (fun a x -> a@[S x]) [Dot] l in
                            let new_item = (s,item_body) in
                            (make_item tl x (BatSet.add new_item items))
              else (make_item tl x items)
              

(* recursive closure func *)
let rec closure_r : production -> state -> state -> state
=fun p items w ->
if w = BatSet.empty then items
else let (hd,tl) = BatSet.pop w in 
     let (s,l) = hd in
     let x = (after_dot_symbol l) in
     match x with
        |Dot | S End-> raise (Failure "error") 
        |S (N x) -> let new_items = (make_item p (N x) items) in
                    closure_r p new_items (BatSet.union tl (BatSet.diff new_items items)) 
        |S (T x) -> closure_r p items tl
        |S Epsilon -> closure_r p items tl


(* closure func *)
let closure : production -> state -> state
=fun p items -> (closure_r p items items)




(* //////GOTO//////*)
(* find all items that after_dot_symbol = x *)
let rec find_related_items : state -> symbol -> state -> state
=fun w x a->
if (w=BatSet.empty) then a
else let (hd,tl) = BatSet.pop w in
     let (s,l) = hd in
     if (S x) = (after_dot_symbol l) then (find_related_items tl x (BatSet.add hd a))
     else (find_related_items tl x a)



let rec advance_dot : item_symbol list -> item_symbol list
=fun l->
match l with
|[] -> raise (Failure "no dot to advance")
|hd::tl -> if (hd=Dot) then (try [List.hd tl] with _ -> [])@(Dot::(try List.tl tl with _ -> []))
           else hd::(advance_dot tl)


let goto : production -> state -> symbol -> state
=fun p items x ->
let x_items = (find_related_items items x BatSet.empty) in
let move_dot_items = BatSet.fold (fun (s,l) a -> BatSet.add (s,advance_dot l) a) x_items BatSet.empty in
(closure p move_dot_items)


(* ///////build automaton///// *)
(* A->a.Bb find every B for one state *)
let symbols : state -> symbol BatSet.t
=fun items ->
BatSet.fold (fun (s,l) a-> let item_symbol = (after_dot_symbol l) in
                           match item_symbol with
                           |Dot -> raise (Failure "no dot after dot")
                           |S x-> if (x = Epsilon) || (x = End) then a else (BatSet.add x a) )items BatSet.empty

(* update automaton with each symbol x // i--(x)-->j *)
let one_symbol_step : production -> state -> symbol -> automaton -> automaton
=fun p i x (s, e) ->
let j = (goto p i x) in 
((BatSet.add j s) , (BatSet.add (i,x,j) e))


let rec make_automaton_r : production -> state BatSet.t -> automaton -> automaton
=fun p w (states, edges) ->
if (w=BatSet.empty) then (states,edges)
else let (state,tl) = (BatSet.pop w) in
     let x_set = symbols state in
     let new_automaton = (BatSet.fold (fun x a-> (one_symbol_step p state x a)) x_set (states,edges)) in
     let (new_s, new_e) = new_automaton in
     (make_automaton_r p (BatSet.union tl (BatSet.diff new_s states)) new_automaton)



let make_automaton : cfg -> automaton
=fun cfg -> 
let (n,t,s,p) = cfg in
let ag = (N "fake_start", [s])::p in
let is = BatSet.singleton (N "fake_start", [Dot; S s]) in
let initial_states = BatSet.singleton (closure ag is) in
let initial_edges = BatSet.empty in 
(make_automaton_r ag initial_states (initial_states,initial_edges))





(* ==============(2) convert automaton to parse table======================== *)
let rec item_to_pr : item_symbol list -> symbol list
=fun l ->
match l with
|[]-> []
|Dot::tl -> item_to_pr tl
|S x::tl -> x::(item_to_pr tl)



let check_one_state : follow_set -> state -> table -> bool -> (table * bool)
=fun fs state table b ->
let end_dot_items = BatSet.fold (fun (s,l) a-> if (after_dot_symbol l)=S Epsilon then (BatSet.add (s,l) a) else a) state BatSet.empty in
if BatSet.empty = end_dot_items then (table, b&&true) else 
let (hd,tl) = BatSet.pop end_dot_items in
if not (tl = BatSet.empty) then (table,b&&false) 
else let (s,l) = hd in
     if (s = N "fake_start") then ( if BatMap.mem (state,End) table then (table ,b&&false) else ((BatMap.add (state,End) Acc table),b&&true) )
     else let y = try BatMap.find s fs with _ -> BatSet.empty in
          let pr = (s,item_to_pr l) in
          BatSet.fold (fun x (table ,b) -> if BatMap.mem (state,x) table then (table ,b&&false) else ((BatMap.add (state,x) (Reduce pr) table),b&&true)) y (table,b)


let make_table : cfg -> automaton -> (table*bool)
=fun cfg (states,edges) ->
let follow_set = (follow cfg) in
let empty_table = BatMap.empty in
let update_with_edges = BatSet.fold (fun (i,x,j) a-> match x with
                                                    |T s -> BatMap.add (i,x) (Shift j) a
                                                    |N s -> BatMap.add (i,x) (Goto j) a 
                                                    |Epsilon |End -> raise (Failure "error") ) edges empty_table in
let update_with_states = BatSet.fold (fun x (t,b) -> check_one_state follow_set x t b ) states (update_with_edges,true) in                                                    
update_with_states


(* =================(3) parsing ==================================== *)
let check_SLR : cfg -> bool
=fun cfg -> 
let automaton = make_automaton cfg in
let (table,bool) = make_table cfg automaton in 
bool


let rec stack_pop
=fun stack n ->
if (n>0) then stack_pop (try List.tl stack with _ -> []) (n-1)
else (if (n=0) then stack else raise (Failure "false"))



let rec parse_r : state list -> symbol list -> table -> bool
=fun stack str table->
if str = [] then false 
else let input = List.hd str in
match stack with
|[] ->  false
|hd::tl -> if not (BatMap.mem (hd,input) table) then false
           else match (BatMap.find (hd,input) table) with
                |Acc -> true
                |Goto x -> raise (Failure "wrong table")
                |Shift x -> parse_r (x::stack) (List.tl str) table
                |Reduce (s,l) -> let pop = stack_pop stack (List.length l) in
                                 if (pop = []) then  false
                                 else let new_top = List.hd pop in
                                      if not (BatMap.mem (new_top, s) table) then  false
                                      else (match (BatMap.find (new_top, s) table) with
                                           |Acc -> raise (Failure "wrong table")
                                           |Reduce pr-> raise (Failure "wrong table")
                                           |Goto x | Shift x-> parse_r (x::pop) str table )
                                      


let parse : cfg -> symbol list -> bool
=fun cfg sentence -> 
let (n,t,s,p) = cfg in
let ag = (N "fake_start", [s])::p in
let is = BatSet.singleton (N "fake_start", [Dot; S s]) in
let initial_state = (closure ag is) in
let automaton = make_automaton cfg in
let (table,bool) = make_table cfg automaton in
if bool = false then false
else let stack = [initial_state] in
     (parse_r stack sentence table)



