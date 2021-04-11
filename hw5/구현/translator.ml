type num_cnt = (int ref * int ref)   (* temp_var num * label num *)

let make_new_int : int ref -> int
=fun cnt ->
let temp = !cnt in
let _ = cnt := !cnt +1 in temp

let rec translate_decl : S.decls -> T.program -> T.program
=fun decl_list a ->
if decl_list = [] then a
else (let (typ,id) = List.hd decl_list in
     let instr =( match typ with
                |S.TINT -> T.COPYC (id,0)
                |S.TARR n -> T.ALLOC (id, n) ) in
     let labeledinstr = (T.dummy_label, instr) in 
     (translate_decl (List.tl decl_list) (a@[labeledinstr]) ) )



let rec translate_exp : S.exp -> num_cnt -> (T.var * T.program)
=fun e nc ->
let (tc,lc) = nc in
match e with
|S.NUM n -> let t = "t"^(string_of_int (make_new_int tc)) in
          (t, [(T.dummy_label, T.COPYC (t, n))])
|S.LV (S.ID id) -> let t = "t"^(string_of_int (make_new_int tc)) in
               (t,[(T.dummy_label, T.COPY (t, id))])
|S.LV (S.ARR (id,exp)) -> let (t1, code) =  (translate_exp exp nc) in     
                     let t2 = "t"^(string_of_int (make_new_int tc)) in
                     (t2, code@[(T.dummy_label, T.LOAD (t2, (id, t1)))])
|S.ADD (e1, e2) -> (trans_bop e1 e2 T.ADD nc)
|S.SUB (e1, e2) -> (trans_bop e1 e2 T.SUB nc)
|S.MUL (e1, e2) -> (trans_bop e1 e2 T.MUL nc)
|S.DIV (e1, e2) -> (trans_bop e1 e2 T.DIV nc)
|S.LT  (e1, e2) -> (trans_bop e1 e2 T.LT  nc)
|S.LE  (e1, e2) -> (trans_bop e1 e2 T.LE  nc)
|S.GT  (e1, e2) -> (trans_bop e1 e2 T.GT  nc)
|S.GE  (e1, e2) -> (trans_bop e1 e2 T.GE  nc)
|S.EQ  (e1, e2) -> (trans_bop e1 e2 T.EQ  nc)
|S.AND (e1, e2) -> (trans_bop e1 e2 T.AND nc)
|S.OR  (e1, e2) -> (trans_bop e1 e2 T.OR  nc)
|S.MINUS e -> (trans_uop e T.MINUS nc)
|S.NOT e -> (trans_uop e T.NOT nc)

and trans_bop : S.exp -> S.exp -> T.bop ->  num_cnt -> (T.var * T.program)
=fun e1 e2 bop (tc,lc) ->
let (t1,code1) = (translate_exp e1 (tc,lc)) in 
let (t2,code2) = (translate_exp e2 (tc,lc)) in 
let t3 = "t"^(string_of_int (make_new_int tc)) in 
(t3, code1@code2@[(T.dummy_label, T.ASSIGNV (t3,bop,t1,t2))])

and trans_uop : S.exp -> T.uop -> num_cnt -> (T.var * T.program)
=fun e uop (tc,lc) ->
let (t1,code1) = (translate_exp e (tc,lc)) in 
let t2 = "t"^(string_of_int (make_new_int tc)) in
(t2, code1@[(T.dummy_label, T.ASSIGNU (t2, uop, t1))])



let rec translate_block : S.program -> num_cnt -> T.program
=fun s nc-> 
let (decl_list , stmt_list) = s in
let translated_decls = (translate_decl decl_list []) in
let translated_stmts = (translate_stmt stmt_list [] nc) in
(translated_decls @ translated_stmts)


and  translate_stmt : S.stmts -> T.program ->num_cnt -> T.program
=fun stmt_list a nc-> 
match stmt_list with
|[] -> a
|hd::tl -> (translate_stmt tl (a@(translate_one_stmt hd nc)) nc)

and  translate_one_stmt : S.stmt -> num_cnt -> T.program 
=fun stmt nc->
let (tc,lc) = nc in
match stmt with
|S.ASSIGN (lv,exp) -> (match lv with
                      |S.ID x -> let (t,code) = (translate_exp exp nc) in 
                                 code@[(T.dummy_label , T.COPY (x,t))]
                      |S.ARR (x,e) -> let (t1,code1) = (translate_exp e nc) in 
                                      let (t2,code2) = (translate_exp exp nc) in
                                      code1@code2@[(T.dummy_label, T.STORE ((x,t1),t2))])
|S.READ id -> [(T.dummy_label, T.READ id)]
|S.PRINT e -> let (t,code) = (translate_exp e nc) in
              code@[(T.dummy_label, T.WRITE t)] 
|S.IF (e,s1,s2) -> let (t1,code1) = (translate_exp e nc) in 
                   let codet = (translate_one_stmt s1 nc) in 
                   let codef = (translate_one_stmt s2 nc) in 
                   let lt = (make_new_int lc) in
                   let lf = (make_new_int lc) in
                   let lx = (make_new_int lc) in
                   (code1@[(T.dummy_label, T.CJUMP (t1, lt));(T.dummy_label, T.UJUMP lf);(lt, T.SKIP)]@codet
                   @[(T.dummy_label, T.UJUMP lx);(lf, T.SKIP)]@codef@[(T.dummy_label, T.UJUMP lx); (lx, T.SKIP)])
|S.WHILE (e,s) ->  let (t1,code1) = (translate_exp e nc) in 
                   let codeb = (translate_one_stmt s nc) in
                   let le = (make_new_int lc) in
                   let lx = (make_new_int lc) in 
                   [(le, T.SKIP)]@code1@[(T.dummy_label, T.CJUMPF (t1, lx))]@codeb@[(T.dummy_label, UJUMP le); (lx, T.SKIP)]
|S.DOWHILE (s,e) -> (translate_one_stmt s nc)@(translate_one_stmt (S.WHILE (e,s)) nc) 
|S.BLOCK block -> (translate_block block nc)                          


let translate : S.program -> T.program
=fun s -> 
let tempvar_num = ref 0 in
let label_num = ref 1 in
let nc = (tempvar_num, label_num) in
(translate_block s nc)@[(T.dummy_label, T.HALT)]

 