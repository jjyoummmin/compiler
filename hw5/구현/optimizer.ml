type cfg_block = INSTR of T.linstr | ENTRY | EXIT
type id = int
type cfg_node = (int * cfg_block) 
type cfg_edges = (cfg_node  , cfg_node list) PMap.t 
type cfg = (cfg_node list * cfg_edges)

type def = (cfg_node * T.var)
module Def_set = Set.Make(struct type t = def let compare = compare end)
type rda = (cfg_node, Def_set.t) PMap.t   (* type for in/out/gen/kill *)

module Var_set = Set.Make(struct type t = T.var let compare = compare end)
type lv = (cfg_node, Var_set.t) PMap.t      (* type for in/out/use/def *)

(* ============================ make control flow graph (control_flow )=================================== *)
let incremented_cnt : int ref -> int
=fun cnt ->
let _ = cnt := !cnt + 1 in
!cnt


let find_node_with_block : cfg_block -> cfg_node list -> cfg_node
= fun block t ->
let map = List.fold_left (fun a (id,b) -> PMap.add b id a ) PMap.empty t in
let id = try (PMap.find block map) with _ -> 0 in
(id, block)

(* for edge (~ goto l) --> (l : instr) *)
(* find (id, l : instr) *)
let rec find_labeledlistr : T.program -> cfg_node list -> T.label -> cfg_node
=fun pgm t l ->
match pgm with
|[] -> raise (Failure "no matched label in given program")
|(label,instr)::tl -> if (label = l) then 
(let block = (INSTR (label,instr)) in 
(find_node_with_block block t))
else (find_labeledlistr tl t l)



let make_cfg_nodes : T.program -> cfg_node list
=fun t -> 
let id_cnt = ref 0 in
let id1 = incremented_cnt id_cnt in
let pgm_to_nodes = List.fold_left (fun a x ->
let id = incremented_cnt id_cnt in
 a@[(id, INSTR x)]) [] t in
let id2 = incremented_cnt id_cnt in
[(id1,ENTRY)]@pgm_to_nodes@[(id2,EXIT)]


let rec make_cfg_edges : T.program -> cfg_node list ->cfg_node list -> cfg_edges -> cfg_edges
=fun pgm t list a -> 
if list = [] then a else
(let hd = (List.hd list) in
let tl = (List.tl list) in
match hd with
|(id,INSTR (l, T.UJUMP x)) -> let new_edges = ( PMap.add hd [(find_labeledlistr pgm t x)] a ) in (make_cfg_edges pgm t tl new_edges)
|(id, INSTR (l, T.CJUMP (y,x))) | (id, INSTR (l, T.CJUMPF (y,x))) -> let new_edges = (PMap.add hd [(List.hd tl);(find_labeledlistr pgm t x)] a) in
                                                         (make_cfg_edges pgm t tl new_edges)
|(id,EXIT) -> a
|_ -> let new_edges = (PMap.add hd [(List.hd tl)] a) in (make_cfg_edges pgm t tl new_edges))                                                         



let control_flow : T.program -> cfg
= fun t -> 
let nodes = (make_cfg_nodes t) in
let edges = (make_cfg_edges t nodes nodes PMap.empty ) in
(nodes,edges)

(* ========================================= cfg printer for testing ========================================================= *)
let string_of_instr : T.linstr -> string
=fun labeledinstr -> 
  let s_bop o = match o with T.ADD -> "+" | T.SUB -> "-" | T.MUL -> "*" | T.DIV -> "/"
  | T.LT -> "<" | T.LE -> "<=" | T.GT -> ">" | T.GE -> ">=" | T.EQ -> "==" | T.AND -> "&&" |
  T.OR -> "||" in
  let s_uop o = match o with T.MINUS -> "-" | T.NOT -> "!" in
  let s_arr (x,y) = x ^ "[" ^ y ^ "]" in
  let (label, instr) = labeledinstr in
    (string_of_int label ^ " : " ^
    (match instr with
    | T.HALT -> "HALT"
    | T.SKIP -> "SKIP"
    | T.ALLOC (x,n) -> (x ^ " = alloc (" ^ string_of_int n ^ ")")
    | T.ASSIGNV (x,o,y,z) -> (x ^ " = " ^ y ^ " " ^ s_bop o ^ " " ^ z)
    | T.ASSIGNC (x,o,y,n) -> (x ^ " = " ^ y ^ " " ^ s_bop o ^ " " ^ string_of_int n)
    | T.ASSIGNU (x,o,y) -> (x ^ " = " ^ s_uop o ^ y)
    | T.COPY (x,y) -> (x ^ " = " ^ y)
    | T.COPYC (x,n) -> (x ^ " = " ^ string_of_int n)
    | T.UJUMP label -> ("goto " ^ string_of_int label)
    | T.CJUMP (x,l) -> ("if " ^ x ^ " goto " ^ string_of_int l)
    | T.CJUMPF (x,l) -> ("iffalse " ^ x ^ " goto " ^ string_of_int l)
    | T.LOAD (x,a) -> (x ^ " = " ^ s_arr a)
    | T.STORE (a,x) -> (s_arr a ^  " = " ^ x)
    | T.READ x -> ("read " ^ x)
    | T.WRITE x -> ("write " ^ x) ) )
 

let string_of_node : cfg_node -> string
=fun (id,block) ->  
let b = match block with
|ENTRY ->  "ENTRY" 
|EXIT ->   "EXIT" 
|INSTR instr -> (string_of_instr instr) in
(string_of_int id ^ "|" ^b)

let print_edges : cfg_edges -> unit
=fun edges ->
PMap.iter (fun node1 node2 ->  let str_n2 = (List.fold_left (fun a x -> a ^ ", " ^ (string_of_node x)) "[" node2)  ^ " ]"in
                               let str = (string_of_node node1) ^ "  -->  " ^ (str_n2) in
                                 (print_endline str) ) edges


let cfg_printer : cfg -> unit
=fun (nodes, edges) ->
let _ = print_endline "===nodes===" ; (List.iter (fun x -> print_endline (string_of_node x)) nodes) in
let _ = print_endline "===edges===" ; (print_edges edges) in () 



(* ====================================(1) reaching definition analysis ============================================== *)
let add_def : cfg_node -> Def_set.t -> Def_set.t
=fun node a -> 
let (id ,block) = node in
match block with
|INSTR (label, instr) ->
(match instr with
| T.ALLOC (x,n) -> Def_set.add (node,x) a
| T.ASSIGNV (x,o,y,z) -> Def_set.add (node,x) a
| T.ASSIGNC (x,o,y,n) -> Def_set.add (node,x) a
| T.ASSIGNU (x,o,y) -> Def_set.add (node,x) a
| T.COPY (x,y) -> Def_set.add (node,x) a
| T.COPYC (x,n)  -> Def_set.add (node,x) a 
| T.LOAD (x,y) -> Def_set.add (node,x) a
| T.STORE ((x,i),y) -> Def_set.add (node,x) a
| _ -> a)
|_ -> a

let find_all_def : cfg -> Def_set.t
=fun (nodes,edges) -> List.fold_left (fun a x -> add_def x a) Def_set.empty nodes

let compute_gen : cfg -> rda
=fun (nodes, edges) -> 
List.fold_left (fun a x -> 
let (id,block) = x in
match block with
| ENTRY | EXIT -> PMap.add x Def_set.empty a
| INSTR instr -> PMap.add x (add_def x Def_set.empty) a
) PMap.empty nodes

let compute_kill : cfg -> rda
=fun (nodes, edges) -> 
let all_def = find_all_def (nodes,edges) in

List.fold_left (fun a x -> 
let self = (add_def x Def_set.empty) in
if (Def_set.is_empty self) then PMap.add x self a else 

(let (self_node, self_var) = try Def_set.choose self with _ -> raise (Failure "empty set") in
let same_var_def = Def_set.fold (fun (node, var) a -> 
if var = self_var then Def_set.add (node,var) a else a
) all_def Def_set.empty in
PMap.add x (Def_set.diff same_var_def self) a )

) PMap.empty nodes


let find_predecessors : cfg -> cfg_node -> cfg_node list
=fun (nodes, edges) node ->
PMap.foldi (fun p_node node_list a ->
if (List.mem node node_list) then (p_node::a)
else a
) edges []


(* one iteration *)
let rec rda_equation : cfg -> rda -> rda ->rda ->rda -> (rda * rda)   
=fun cfg gen kill in_before out_before ->
let (nodes, edges) = cfg in
let (in_after, out_after) = List.fold_left ( fun (in1,out1) node -> 

let p = (find_predecessors cfg node) in
let new_in_set = List.fold_left (fun a x ->
let out_x =  try (PMap.find x out1) with _ -> raise (Failure "no out_set found for given block") in 
(Def_set.union out_x a)
) Def_set.empty p in
let gen_node = try (PMap.find node gen) with _ -> raise (Failure "no gen_set found for given block") in
let kill_node = try (PMap.find node kill) with _ -> raise (Failure "no kill_set found for given block") in
let new_out_set = Def_set.union gen_node (Def_set.diff new_in_set kill_node) in
(PMap.add node new_in_set in1, PMap.add node new_out_set out1)

) (in_before,out_before) nodes in

let no_change = List.for_all (fun node -> 
let in1 = try (PMap.find node in_before) with _ -> raise (Failure "no in_set in old_in") in
let in2 = try (PMap.find node in_after) with _ -> raise (Failure "no in_set in new_in") in
(Def_set.equal in1 in2)
) nodes in
if no_change then (in_after, out_after)
else (rda_equation cfg gen kill in_after out_after)



(* input: cfg => output : (in,out) *)
let rda_solve : cfg -> (rda * rda)
=fun cfg ->
let (nodes,edges) = cfg in
let gen = compute_gen cfg in
let kill = compute_kill cfg in
let initial_in = List.fold_left (fun a x -> PMap.add x Def_set.empty a) PMap.empty nodes in
let initial_out = List.fold_left (fun a x -> PMap.add x Def_set.empty a) PMap.empty nodes in
(rda_equation cfg gen kill initial_in initial_out)

(* ===printer==== *)
let string_of_defset : Def_set.t -> string
=fun set ->
(Def_set.fold (fun (node,var) a ->  a^", ("^ var ^" || "^ string_of_node node ^")") set "{" ) ^ " }"

let rda_printer : cfg -> unit
=fun cfg ->
let (nodes, edges) = cfg in
let (rda_in, rda_out) = rda_solve cfg in
List.iter (fun node -> 
let in_set = try (PMap.find node rda_in) with _ -> raise (Failure "no in_set found") in
let out_set = try (PMap.find node rda_out) with _ -> raise (Failure "no out_set found") in
let str = (string_of_node node) ^"     |   => IN " ^(string_of_defset in_set) ^" , OUT " ^(string_of_defset out_set) in 
print_endline str
) nodes

let kill_printer : cfg -> unit
=fun cfg ->
let (nodes, edges) = cfg in
let kill = compute_kill cfg in
List.iter (fun node -> 
let kill_node = try (PMap.find node kill) with _ -> raise (Failure "error") in
let str = (string_of_node node) ^"     |   => KILL " ^(string_of_defset kill_node) in 
print_endline str
) nodes

let gen_printer : cfg -> unit
=fun cfg ->
let (nodes, edges) = cfg in
let gen = compute_gen cfg in
List.iter (fun node -> 
let gen_node = try (PMap.find node gen) with _ -> raise (Failure "error") in
let str = (string_of_node node) ^"     |   => GEN " ^(string_of_defset gen_node) in 
print_endline str
) nodes


(* ======================================= (2) liveness analysis =================================================== *)
let compute_def_use : cfg -> (lv * lv)
=fun cfg ->
let (nodes,edges) =  cfg in
List.fold_left (fun (def,use) (id,block) -> 
let (def_var_list, use_var_list) = 
(match block with
|INSTR (label, instr) ->
(match instr with
| T.ALLOC (x,n) -> ([x],[])
| T.ASSIGNV (x,o,y,z) -> ([x],[y;z])
| T.ASSIGNC (x,o,y,n) -> ([x],[y])
| T.ASSIGNU (x,o,y) -> ([x],[y])
| T.COPY (x,y) -> ([x],[y])
| T.COPYC (x,n)  -> ([x],[])
| T.LOAD (x,(y,i)) -> ([x],[y;i])
| T.STORE ((x,i),y) -> ([x],[i;y])
| T.CJUMP (x,l) -> ([],[x])
| T.CJUMPF (x,l) -> ([],[x])
| T.READ x -> ([],[x])
| T.WRITE x -> ([],[x])
| _ -> ([],[]))
|_ -> ([],[]) ) in
let def_node = List.fold_left (fun a x -> Var_set.add x a) Var_set.empty def_var_list in
let use_node = List.fold_left (fun a x -> Var_set.add x a) Var_set.empty use_var_list in
(PMap.add (id,block) def_node def, PMap.add (id,block) use_node use)
) (PMap.empty, PMap.empty) nodes 


let find_successors : cfg -> cfg_node -> cfg_node list
=fun (nodes, edges) node -> match node with
|(id,EXIT) -> []
|_ -> try (PMap.find node edges) with _ -> raise (Failure "cannot find successors")




(* one iteration *)
let rec lv_equation : cfg -> lv -> lv ->lv ->lv -> (lv * lv)   
=fun cfg def use in_before out_before ->
let (nodes, edges) = cfg in
let (in_after, out_after) = List.fold_left ( fun (in1,out1) node -> 

let s = (find_successors cfg node) in
let new_out_set = List.fold_left (fun a x ->
let in_x =  try (PMap.find x in1) with _ -> raise (Failure "no in_set found for given block") in 
(Var_set.union in_x a)
) Var_set.empty s in
let def_node = try (PMap.find node def) with _ -> raise (Failure "no def_set found for given block") in
let use_node = try (PMap.find node use) with _ -> raise (Failure "no use_set found for given block") in
let new_in_set = Var_set.union use_node (Var_set.diff new_out_set def_node) in
(PMap.add node new_in_set in1, PMap.add node new_out_set out1)

) (in_before,out_before) (List.rev nodes) in

let no_change = List.for_all (fun node -> 
let out1 = try (PMap.find node out_before) with _ -> raise (Failure "no out_set in old_out") in
let out2 = try (PMap.find node out_after) with _ -> raise (Failure "no out_set in new_out") in
(Var_set.equal out1 out2)
) nodes in
if no_change then (in_after, out_after)
else (lv_equation cfg def use in_after out_after)


(* input: cfg => output : (in,out) *)
let lv_solve : cfg -> (lv * lv)
=fun cfg ->
let (nodes,edges) = cfg in
let (def,use) = compute_def_use cfg in
let initial_in = List.fold_left (fun a x -> PMap.add x Var_set.empty a) PMap.empty nodes in
let initial_out = List.fold_left (fun a x -> PMap.add x Var_set.empty a) PMap.empty nodes in
(lv_equation cfg def use initial_in initial_out)

(* ===printer==== *)
let string_of_varset : Var_set.t -> string
=fun set ->
(Var_set.fold (fun x a ->  a^", "^x) set "{" ) ^ " }"

let lv_printer : cfg -> unit
=fun cfg ->
let (nodes, edges) = cfg in
let (lv_in, lv_out) = lv_solve cfg in
List.iter (fun node -> 
let in_set = try (PMap.find node lv_in) with _ -> raise (Failure "no in_set found") in
let out_set = try (PMap.find node lv_out) with _ -> raise (Failure "no out_set found") in
let str = (string_of_node node) ^"     |   => IN " ^(string_of_varset in_set) ^" , OUT " ^(string_of_varset out_set) in 
print_endline str
) nodes

(* ================================ APPLICATION ====================================== *)

(* (1) replace var wtih var or constant / USE RDA *)
let replace_with_constant : T.linstr -> Def_set.t -> T.var -> T.linstr
=fun line in_set var->
let (label, instr) = line in
let constant_list = Def_set.fold (fun (nn, v) a -> match nn with
|(id, INSTR (label, T.COPYC (x,n))) -> if (var=v) then (n::a) else a 
|_ -> a  
) in_set [] in
if constant_list = [] then line else
(
let constant = List.hd constant_list in
let valid = List.for_all (fun x -> x = constant) constant_list in
if not valid then line else
match instr with
| T.ASSIGNV (x,o,z,y) ->  (label, T.ASSIGNC (x,o,z,constant))
| T.COPY (x,y) ->  (label, T.COPYC (x,constant))
|_ -> raise (Failure "error in constant replacement")
)


 let replace_with_var : T.linstr -> Def_set.t -> T.var -> T.linstr
=fun line in_set var->
let (label, instr) = line in
let variable_list = Def_set.fold (fun (nn, v) a -> match nn with
|(id, INSTR (label, T.COPY (x,y))) -> if (var=v) then (y::a) else a 
|_ -> a  
) in_set [] in
if variable_list = [] then line else
(
let variable = List.hd variable_list in
let valid = List.for_all (fun x -> x = variable) variable_list in
if not valid then line else
match instr with
| T.ASSIGNV (x,o,y,z) -> if (var=y) then (label, T.ASSIGNV (x,o,variable,z)) else (label, T.ASSIGNV (x,o,y,variable)) 
| T.ASSIGNC (x,o,y,n) -> (label, T.ASSIGNC (x,o,variable,n))
| T.ASSIGNU (x,o,y) -> (label, T.ASSIGNU (x,o,variable))
| T.COPY (x,y) -> (label, T.COPY (x, variable))
| T.LOAD (x,(y,i)) -> (label, T.LOAD (x, (y, variable)))
| T.STORE ((x,i),y) -> if (var=y) then (label, T.STORE ((x,i),variable)) else (label, T.STORE ((x,variable),y)) 
| T.CJUMP (x,l) -> (label, T.CJUMP (variable,l))
| T.CJUMPF (x,l) -> (label, T.CJUMPF (variable,l))
| T.READ x -> (label, T.READ (variable))
| T.WRITE x -> (label, T.WRITE (variable))
|_ -> raise (Failure "error in variable replacement")
)


let constant_propagation : T.program -> T.program
=fun pgm ->
let pgm_cnt = ref 1 in
let cfg = control_flow pgm in
let (in_rda, out_rda) = rda_solve cfg in
List.fold_left (fun a line ->
let (label, instr) = line in
let id = incremented_cnt pgm_cnt in
let node = (id, INSTR (label, instr)) in
let in_set =  try (PMap.find node in_rda) with _ -> raise (Failure "no in_set found") in
let new_line = (match instr with
| T.ASSIGNV (x,o,z,y) -> (replace_with_constant line  in_set y)
| T.COPY (x,y) -> (replace_with_constant line  in_set y)
|_ -> line)  in
let ( _, new_instr) = new_line in
(match new_instr with
T.ASSIGNV (x,o,y,z) ->  let new_line2 = (replace_with_var new_line in_set y) in a@[(replace_with_var new_line2 in_set z)]
| T.ASSIGNC (x,o,y,n) -> a@[(replace_with_var new_line in_set y)]
| T.ASSIGNU (x,o,y) -> a@[(replace_with_var new_line in_set y)]
| T.COPY (x,y) -> a@[(replace_with_var new_line in_set y)]
| T.LOAD (x,(y,i)) -> a@[(replace_with_var new_line in_set i)]
| T.STORE ((x,i),y) -> let new_line2 = (replace_with_var new_line in_set y) in a@[(replace_with_var new_line2 in_set i)] 
| T.CJUMP (x,l) -> a@[(replace_with_var new_line in_set x)]
| T.CJUMPF (x,l) -> a@[(replace_with_var new_line in_set x)]
| T.READ x -> a@[(replace_with_var new_line in_set x)]
| T.WRITE x -> a@[(replace_with_var new_line in_set x)]
| _ -> a@[new_line]
) ) [] pgm


(* (2) erase deadcode / USE LV *)


let check_if_dead : T.var -> cfg_node -> lv -> lv -> bool
=fun x node in_lv out_lv->
let in_set =  try (PMap.find node in_lv) with _ -> raise (Failure "no in_set found") in
let out_set =  try (PMap.find node out_lv) with _ -> raise (Failure "no out_set found") in
let diff = Var_set.diff out_set in_set in
(if (Var_set.mem x diff) then false
else true)


let dead_def_elimination : T.program -> T.program
=fun pgm ->
let pgm_cnt = ref 1 in
let cfg = control_flow pgm in
let (in_lv, out_lv) = lv_solve cfg in

List.fold_left (fun a line -> 
let (label, instr) = line in
let id = incremented_cnt pgm_cnt in
let node = (id, INSTR line) in
let dead = (match instr with
| T.ASSIGNV (x,o,y,z) -> (check_if_dead x node in_lv out_lv)
| T.ASSIGNC (x,o,y,n) -> (check_if_dead x node in_lv out_lv)
| T.ASSIGNU (x,o,y) -> (check_if_dead x node in_lv out_lv)
| T.COPY (x,y) -> (check_if_dead x node in_lv out_lv)
| T.COPYC (x,n)  -> (check_if_dead x node in_lv out_lv)
| T.LOAD (x,(y,i)) -> (check_if_dead x node in_lv out_lv)
| _ -> false) in
if dead then a else a@[line]
) [] pgm


let optimize : T.program -> T.program
=fun t -> 
let optimized1 = (constant_propagation t) in
let optimized2 = (dead_def_elimination optimized1) in
optimized2
