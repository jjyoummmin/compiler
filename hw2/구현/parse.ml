type symbol = T of string | N of string | Epsilon | End
type production = (symbol * symbol list) list
type cfg = symbol list * symbol list * symbol * production
type first_set = (symbol, symbol BatSet.t) BatMap.t
type follow_set = (symbol, symbol BatSet.t) BatMap.t
type table = ((symbol * symbol) ,  production) BatMap.t
type dependency = (symbol , symbol BatSet.t) BatMap.t


(* /////////////(1)finding first set//////////////////// *)

(* printer *)
(* symbol -> string *)
let string_of_symbol s = 
match s with
|T x -> x
|N x -> x
|Epsilon -> "epsilon"
|End -> "$"

(* symbol list -> string *)
let string_of_list l = 
let str = "[" in
let str2 = List.fold_left (fun a x -> a ^ ", " ^(string_of_symbol x)) str l in
(str2^" ]")

(* symbol BatSet.t -> string *)
let string_of_set set =
  "{ " ^ (BatSet.fold (fun s str -> str ^ string_of_symbol s ^ ", ") set "") ^ " }"


(* printer for first/follow set *)
let set_printer set = 
    BatMap.iter (fun s symbols -> 
      prerr_endline (string_of_symbol s ^ " -> " ^ string_of_set symbols  )
    ) set

(* production -> string *)
let string_of_pr pr = 
let str = "{ " in
let str2 = List.fold_left (fun str (s,l) -> str ^ string_of_symbol s ^ "->" ^ string_of_list l ^ ", ") str pr in
(str2^" }")


(* printer for parse table *)
let table_printer t = 
    BatMap.iter (fun (a,b) pr ->
    prerr_endline ("(" ^ string_of_symbol a ^"," ^ string_of_symbol b ^ ")  =>" ^ string_of_pr pr))  t  


(* //////////////////////////// *)

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
(* for production rule (s,l)
    if l=[] then add epsilon to first(s)
    else {
         if first symbol of l is terminal, then add that terminal symbol to first(s)
         else first symbol of l is non-terminal nt {
                if first(nt) not completed then w@[(s,l)] (send this p-rule to the end of worklist /  check this by find_nonterm func)
                else union first(nt) to first(s) + if epsilon is member of first(nt) add p-rule (s,tl of body) to worklist
            }
         } 
*)
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


(* /////////////////(2) finding follow set////////////////// *)

(* return tl list following target symbol x *)
let rec split_list :symbol -> symbol list -> symbol list
=fun x l ->
match l with
|[]->[]
|hd::tl -> (if x=hd then tl else (split_list x tl))


(* checking one pr of check_pr func *) 
(* 
    if x is end of the string of pr-body (=>after_x_string = []) {
      if(pr-head = x){
          erase x from w and skip..
      }else{
         if(follow(pr-head) not completed (=> s still Member of w)){
             then move x to the end of w and skip..
         }else{
             add follow(s) to follow(x) and erase x from w / move to next pr

         }

      }

    }else{
      next symbol of x = ns
      if(first(ns) contians epsilon){
        add (first(ns)-epsilon) to follow(x) and call check_one_pr with next string of ns

      }else{
         add first(ns) to follow(x) and erase x from w / move to next pr
      }

    }
*)
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

(* ////////////(3)make parse table////////////// *)
let update_table
=fun set s1 s2 ->
  let old = try BatMap.find s1 set with _ -> [] in
  if List.mem s2 old then (BatMap.add s1 old set) 
  else BatMap.add s1 (s2::old) set

(* fill table related to one production-rule *)
(* 
  if production-body = Epsilon (nullable){
      for every x in Follow(s){
        fill table
        M[s,x] = "s -> l"
      }
  }else{
    let first_hd = first symbol of l at production rule (s->l)
    for every x in first(hd){
      fill table
      M[s,x] = "s->l"

      if (first(hd) contains epsilon){
        call iter_one with (s->tl)
      }
    }

  }
 *)
let rec iter_one : (symbol * symbol list) -> (symbol * symbol list) -> first_set -> follow_set -> table -> table
=fun pr (s,l) first follow table->
match l with
|[]-> let follow_s = (BatMap.find s follow) in
      (BatSet.fold (fun x a -> update_table a (s,x) pr) follow_s table) 
|hd::tl -> let first_hd = (BatMap.find hd first) in
           if (BatSet.mem Epsilon first_hd) then 
           (let table2 = (BatSet.fold (fun x a -> update_table a (s,x) pr) (BatSet.remove Epsilon first_hd) table) in
           iter_one pr (s,tl) first follow table2)
           else (BatSet.fold (fun x a -> update_table a (s,x) pr) first_hd table)      


let rec iter_pr : production  -> first_set -> follow_set -> table -> table
=fun w first follow a ->
match w with
|[] -> a
|hd::tl -> let new_table = (iter_one hd hd first follow a) in (iter_pr tl first follow new_table)

let parse_table : cfg -> table
=fun cfg ->
let (n,t,s,p) = cfg in
let first_set = (first cfg) in
let follow_set = (follow cfg) in 
(iter_pr p first_set follow_set BatMap.empty)

(* ///////////////////////////////////////////////////// *)

(* check if given cfg is LL1 grammar *)
let check_LL1 : cfg -> bool
=fun cfg -> 
let table = (parse_table cfg) in
(BatMap.for_all (fun a b -> (List.length b) <= 1) table)



(* recursively check stack-top and front of str *)
let rec parse_r : table -> symbol list -> symbol list -> bool
=fun t stack str-> 
let top = (List.hd stack) in
match top with
|End -> (if List.hd str = End then true else false) 
|(T x) -> if ((T x) = List.hd str) then (parse_r t (List.tl stack) (List.tl str)) else false
|(N x) -> let pr = (try (BatMap.find (top,List.hd str) t) with _ -> []) in 
                        (if pr = [] then false
                        else let (s,l) = (List.hd pr) in (parse_r t (l@(List.tl stack)) str)
                        )
|Epsilon -> raise (Failure "no epsilon appear on production rule it is just []")


(* final parse function *)
let parse : cfg -> symbol list -> bool
=fun cfg sentence -> 
let (n,t,s,p) = cfg in
let initial_stack = [s;End] in 
let table = (parse_table cfg) in
if (check_LL1 cfg) then (parse_r table initial_stack sentence) else false
