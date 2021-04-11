type var = string
type aexp = 
  | Int of int
  | Var of var
  | Plus of aexp * aexp
  | Mult of aexp * aexp 
  | Minus of aexp * aexp 
 
type bexp = 
  | True 
  | False
  | Eq of aexp * aexp 
  | Le of aexp * aexp 
  | Neg of bexp 
  | Conj of bexp * bexp 

type cmd = 
  | Assign of var * aexp 
  | Skip
  | Seq of cmd * cmd
  | If of bexp * cmd * cmd
  | While of bexp * cmd 

(* x:=1; y:=2; a:=x+y; b:=x-y *) 
let test1 = 
  Seq (Assign ("x", Int 1), 
    Seq (Assign ("y", Int 2), 
      Seq (Assign ("a", Plus  (Var "x", Var "y")), 
           Assign ("b", Minus (Var "x", Var "a")))))


(* x:=10; y:=2; while (x!=1) do (y:=y*x; x:=x-1) *)
let test2 = 
  Seq (Assign ("x", Int 10), 
    Seq (Assign("y", Int 2), 
         While (Neg (Eq (Var "x", Int 1)),
                Seq(Assign("y", Mult(Var "y", Var "x")), 
                    Assign("x", Minus(Var "x", Int 1))))))

(* a:=10; b:=2; q:=0; r:=a; while (b<=r) { r:=r-b; q:=q+1 } *)
let test3 = 
  Seq (Assign ("a", Int 10), 
    Seq (Assign ("b", Int 2), 
      Seq (Assign ("q", Int 0), 
        Seq (Assign ("r", Var "a"), 
           While (Le (Var "b", Var "r"),
                Seq(Assign("r", Minus(Var "r", Var "b")), 
                    Assign("q", Plus(Var "q", Int 1))))))))

module ABool = struct
  type t = Bot | Top | TT | FF
  let alpha b = if b then TT else FF

  (* partial order *)
  let order : t -> t -> bool 
  =fun b1 b2 -> if (b1=b2) then true
  else (match (b1,b2) with
  |(Bot,_) -> true
  |(_,Top) -> true
  |_ -> false )

  (* least upper bound *)
  let lub : t -> t -> t 
  =fun b1 b2 -> 
  if (order b1 b2) then b2
  else (if (order b2 b1) then b1 else Top) 

  (* abstract negation *)
  let neg : t -> t 
  =fun b -> match b with
  |TT -> FF
  |FF -> TT
  |_ -> b

  (* abstract conjunction *)
  let conj : t -> t -> t
  =fun b1 b2 -> match (b1,b2) with
  |(Bot,_)|(_,Bot) -> Bot
  |(FF,_)|(_,FF)->FF
  |(TT,TT) -> TT
  |_-> Top
end

module AValue = struct
  type t = Bot | Top | Neg | Zero | Pos | NonPos | NonZero | NonNeg
  let alpha : int -> t 
  =fun n -> if n = 0 then Zero else if n > 0 then Pos else Neg
  let to_string s = 
    match s with 
    | Bot -> "Bot" 
    | Top -> "Top" 
    | Pos -> "Pos" 
    | Neg -> "Neg" 
    | Zero -> "Zero"
    | NonNeg -> "NonNeg"
    | NonZero -> "NonZero"
    | NonPos -> "NonPos"

  (* partial order *)
  let order : t -> t -> bool
  =fun s1 s2 -> if (s1=s2) then true else
  match (s1,s2) with
  |(Bot,_) -> true
  |(_,Top) -> true
  |(Neg,NonPos)|(Neg,NonZero) -> true
  |(Zero,NonPos)|(Zero,NonNeg) -> true
  |(Pos, NonZero)|(Pos,NonNeg) -> true
  |_ -> false


  (* least upper bound *)
  let lub : t -> t -> t 
  =fun s1 s2 -> if (order s1 s2) then s2 else
  (if (order s2 s1) then s1 else 
  (match (s1,s2) with
  |(Neg,Zero)|(Zero,Neg)->NonPos
  |(Neg,Pos)|(Pos,Neg)-> NonZero
  |(Zero,Pos)|(Pos,Zero)->NonNeg
  |_ -> Top
  )) 

    
  (* abstract addition *)
  let plus : t -> t -> t 
  =fun a1 a2 -> if ( (a1=a2) && (not (a1=NonZero))) then a1 else 
  (match (a1,a2) with
  |(Bot,_)|(_,Bot)->Bot
  |(Top,_)|(_,Top)->Top
  |(Zero,x1) ->x1
  |(x1,Zero)->x1
  |(NonPos,Neg)|(Neg,NonPos)->Neg
  |(NonNeg,Pos)|(Pos,NonNeg) -> Pos
  |_->Top 
  )

  (* abstract multiplication *)
  let mult : t -> t -> t 
  =fun a1 a2 -> match (a1,a2) with
  |(Bot,_)|(_,Bot)-> Bot
  |(Zero,_)|(_,Zero)-> Zero
  |(Neg,Neg)|(Pos,Pos)->Pos
  |(Pos,Neg)|(Neg,Pos)->Neg
  |(NonPos,Neg)|(Neg,NonPos)|(NonNeg,Pos)|(Pos,NonNeg)|(NonPos,NonPos)|(NonNeg,NonNeg)->NonNeg
  |(NonNeg,Neg)|(Neg,NonNeg)|(NonPos,Pos)|(Pos,NonPos)|(NonNeg,NonPos)|(NonPos,NonNeg)->NonPos
  |_->Top


  (* abstract subtraction *)
  let minus : t -> t -> t
  =fun a1 a2 -> 
  let neg_a2 = (match a2 with
  |Neg->Pos
  |Pos->Neg
  |NonNeg->NonPos
  |NonPos->NonNeg
  |_->a2) in (plus a1 neg_a2)
    
  let eq : t -> t -> ABool.t 
  =fun a1 a2 -> match (a1,a2) with
  |(Bot,_)|(_,Bot)->ABool.Bot
  |(Zero,Zero)->ABool.TT
  |(Zero,Neg)|(Neg,Zero)|(Pos,Neg)|(Neg,Pos)|(NonNeg,Neg)|(Neg,NonNeg)|(Pos,Zero)|(Zero,Pos)|(NonZero,Zero)|(Zero,NonZero)|(NonPos,Pos)|(Pos,NonPos)->ABool.FF
  |_ -> ABool.Top

  let le : t -> t -> ABool.t 
  =fun a1 a2 -> match (a1,a2) with
  |(Bot,_)|(_,Bot) -> ABool.Bot
  |(Zero,Neg)|(Pos,Neg)|(Pos,Zero)|(Pos,NonPos)|(NonNeg,Neg)|(NonNeg,Zero)->ABool.FF
  |(Neg,NonNeg)|(Zero,Zero)|(Zero,Pos)|(Zero,NonNeg)|(NonPos,Zero)|(NonPos,Pos)|(NonPos,NonNeg)->ABool.TT
  |_ -> ABool.Top
end

module AState = struct
  module Map = Map.Make(struct type t = var let compare = compare end)
  type t = AValue.t Map.t (* var -> AValue.t map *)
  let bot = Map.empty
  let find x m = try Map.find x m with Not_found -> AValue.Bot
  let update x v m = Map.add x v m
  let update_join x v m = Map.add x (AValue.lub v (find x m)) m
  let order m1 m2 = Map.for_all (fun k v -> AValue.order v (find k m2)) m1
  let lub m1 m2 = Map.fold (fun k v m -> update_join k v m) m1 m2
  let print m = 
    Map.iter (fun k v -> 
   print_endline (k ^ " |-> " ^ AValue.to_string v)) m 
end

let rec aeval : aexp -> AState.t -> AValue.t
=fun a s ->
  match a with
  | Int n -> AValue.alpha n 
  | Var x -> AState.find x s 
  | Plus (a1, a2) -> AValue.plus (aeval a1 s) (aeval a2 s)
  | Mult (a1, a2) -> AValue.mult (aeval a1 s) (aeval a2 s)
  | Minus (a1, a2) -> AValue.minus (aeval a1 s) (aeval a2 s)

let rec beval : bexp -> AState.t -> ABool.t
=fun b s -> 
  match b with
  | True -> ABool.alpha true                      (* ABool.TT *)
  | False -> ABool.alpha false                     (* ABool.FF *)
  | Eq (a1, a2) -> AValue.eq (aeval a1 s) (aeval a2 s)
  | Le (a1, a2) -> AValue.le (aeval a1 s) (aeval a2 s)
  | Neg b -> ABool.neg (beval b s)
  | Conj (b1, b2) -> ABool.conj (beval b1 s) (beval b2 s)

let rec ceval : cmd -> AState.t -> AState.t
=fun c s -> 
  match c with
  | Assign (x, a) -> AState.update x (aeval a s) s
  | Skip -> s
  | Seq (c1,c2) -> ceval c2 (ceval c1 s)
  | If (b, c1, c2) -> 
      if beval b s = ABool.TT then (ceval c1 s)
      else if beval b s = ABool.FF then (ceval c2 s)
      else if beval b s = ABool.Bot then AState.bot
      else AState.lub (ceval c1 s) (ceval c2 s)

  | While (b, c) -> fix (ceval (If (b, c, Skip))) s
  
                    
                     
and fix f s0 = if AState.order (f s0) s0 then s0 else fix f (f s0)

let run : cmd -> AState.t
=fun c -> ceval c AState.bot

let _ = List.iter (fun x -> AState.print (run x); print_endline "") [test1;test2;test3]

