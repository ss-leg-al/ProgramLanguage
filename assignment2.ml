exception NotImplemented;;

let rec dropWhile : ('a -> bool) -> 'a list -> 'a list
= fun test lst ->
    match lst with
      |[]->[]
      |hd::tl->
        if not (test hd) then hd::tl
        else dropWhile test tl



(*hd::(dropWhile test tl)*)


let rec sigma : (int -> int) -> int -> int -> int
= fun f a b ->
    if a=b then f b
    else (f a)+(sigma f (a+1) b)



let rec forall : ('a -> bool) -> 'a list -> bool
= fun f lst ->
    match lst with
        |[]->true
        |hd::tl->
          if (f hd) then forall f tl
          else false

let rec checksame list a=
          match list with
            |[]->false
            |hd::tl-> if hd=a then true else checksame tl a 

let rec onlyuniq a tmp=
          match a with
            |[]->tmp
            |hd::tl->if not (checksame tmp hd) then (onlyuniq tl (tmp@[hd])) else (onlyuniq tl tmp)
let uniq : 'a list -> 'a list
= fun lst ->onlyuniq lst []


let rec rev list tmp=
          match list with
            |[]->tmp
            |(hd::tl)->rev tl (hd::tmp)
let fastrev : 'a list -> 'a list
= fun lst->(rev lst [])



type aexp =
  | Const of int
  | Var of string
  | Power of string * int
  | Times of aexp list
  | Sum of aexp list;;

let rec diff : aexp * string -> aexp
= fun (exp, x) ->
    match exp with
      |Const(a)->Const(0)
      |Var(a)->if a=x then Const(1) else Const(0)    
      |Power(a,b)->if b=0 then Const(0)
                      else if a=x then Times([Const(b)]@[Power(a,b-1)])
                         else Const(0)
      |Times(hd::[])->diff(hd,x)
      |Times(hd::tl)->Sum([Times(diff(hd,x)::tl)]@[Times(hd::[diff(Times(tl),x)])])
      |Times([])->Const(0)
      |Sum(hd::[])->diff(hd,x)
      |Sum(hd::tl)->Sum([diff(hd,x)]@[diff(Sum(tl),x)])
      |Sum([])->Const(0)
      
  (*
      diff (Sum([Const 2; Var "x"]),"x");;
      diff (Sum [Times [Const 2; Var "x"]; Const 2],"x");;
      diff (Sum [Power ("x", 2); Times [Const 2; Var "x"]; Const 1],"x");;
      diff (Power ("x", 2),"x");;
*)
type exp =
  | X
  | INT of int
  | ADD of exp * exp
  | SUB of exp * exp
  | MUL of exp * exp
  | DIV of exp * exp
  | SIGMA of exp * exp * exp;;
let rec calsigma p a b c=
    if a=b then p c b
    else (p c a)+(calsigma p (a+1) b c)
let rec plugin f x=
      match f with
          |X->x 
          |INT(a)->a
          |ADD(a,b)->(plugin a x)+(plugin b x)
          |SUB(a,b)->(plugin a x)-(plugin b x)
          |MUL(a,b)->(plugin a x)*(plugin b x)
          |DIV(a,b)->(plugin a x)/(plugin b x)
          |SIGMA(a,b,c)->calsigma (plugin) (plugin a x) (plugin b x) c

let rec calculator : exp -> int
= fun exp ->
    match exp with
      |INT(a)->a
      |X->raise(Failure("?")) 
      |ADD(a,b)->(calculator a)+(calculator b)
      |SUB(a,b)->(calculator a)-(calculator b)
      |MUL(a,b)->(calculator a)*(calculator b)
      |DIV(a,b)->(calculator a)/(calculator b)
      |SIGMA(a,b,c)->calsigma plugin (calculator(a)) (calculator(b)) c
       
      
      
  


     (* calculator (SIGMA(INT 1, INT 10, SUB(MUL(X, X), INT 1)))*)
     (**)
    


(*
let rec acalculator : exp -> int
= fun exp ->
    match exp with
      |INT(a)->a
      |ADD(a,b)->(acalculator a)+(acalculator b)
      |SUB(a,b)->(acalculator a)-(acalculator b)
      |MUL(a,b)->(acalculator a)*(acalculator b)
      |DIV(a,b)->(acalculator a)/(acalculator b)
      |SIGMA(a,b,c)->calsigma (acalculator(a)) (acalculator(b)) c
      |X->raise(Failure("?")) 
      and plugin f k=
          match f with
          |X->k
          |_->plugin f k
      and calsigma a b c=
          if a=b then plugin c b
          else (plugin c a)+(calsigma (a+1) b c)
*)



type exp = 
  | V of var
  | P of var * exp
  | C of exp * exp
and var = string;;
let rec removeall a l=
        match l with
        | []->[]
        |hd::tl->
          if a=hd then removeall a tl
          else hd::(removeall a tl);;
let rec checking exp tmp=
          match exp with
            |V(v)->tmp@[v]
            |P(v,e)->removeall v (checking e tmp)
            |C(e1,e2)->(checking e1 tmp)@(checking e2 tmp)
let check : exp -> bool
= fun exp -> if (checking exp [])=[] then true else false