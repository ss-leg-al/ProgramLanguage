type program = exp
and exp =
    UNIT
  | TRUE
  | FALSE
  | CONST of int
  | VAR of var
  | ADD of exp * exp
  | SUB of exp * exp
  | MUL of exp * exp
  | DIV of exp * exp
  | EQUAL of exp * exp
  | LESS of exp * exp
  | NOT of exp
  | NIL
  | CONS of exp * exp
  | APPEND of exp * exp
  | HEAD of exp
  | TAIL of exp
  | ISNIL of exp
  | IF of exp * exp * exp
  | LET of var * exp * exp
  | LETREC of var * var * exp * exp
  | LETMREC of (var * var * exp) * (var * var * exp) * exp
  | PROC of var * exp
  | CALL of exp * exp
  | PRINT of exp
  | SEQ of exp * exp
and var = string

type typ =
    TyUnit
  | TyInt
  | TyBool
  | TyFun of typ * typ
  | TyList of typ
  | TyVar of tyvar
and tyvar = string

let tyvar_num=ref 0

exception TypeError

(* generate a fresh type variable *)
let fresh_tyvar : unit -> typ = 
  let tyvar_num = ref 0 in
    fun () -> (tyvar_num := !tyvar_num + 1; (TyVar ("t" ^ string_of_int !tyvar_num)))

module TEnv=struct
  type t=var->typ
  let empty=
   fun _ ->raise(TypeError)
  let extend (x,t) tenv=
   fun y -> if x=y then t else (tenv y)
  let find tenv x= tenv x
end

let rec assoc
=fun a lst->
  match lst with
    |((m,n)::tl)->if m=a then n else assoc a tl
    |_->raise(Failure("error"))
let rec map 
= fun f l ->
  match l with
  | [] -> []
  | hd::tl -> (f hd)::(map f tl)


module Subst=struct
  type t= (tyvar*typ) list
  let empty=[]
  let find x subst=(assoc x subst)
  
  
  let rec apply: typ->t->typ
  =fun typ subst->
    match typ with
      |TyUnit->TyUnit
      |TyList x->TyList (apply x subst)
      |TyInt->TyInt
      |TyBool->TyBool
      |TyFun(t1,t2)->
        TyFun((apply t1 subst),(apply t2 subst))
      |TyVar(x)->
        try find x subst
        with _->typ
  let extend tv ty subst=
  (tv,ty)::(map(fun (x,t)->
  (x,apply t [(tv,ty)])) subst)
end

type typ_eqn = (typ * typ) list 

let rec gen_equations
=fun tenv e ty->
  match e with
  |PRINT(a)-> [(ty,TyUnit)]
  |UNIT->[(ty,TyUnit)]
  |TRUE->[(ty,TyBool)]
  |FALSE->[(ty,TyBool)]
  |CONST(a)->[(ty,TyInt)]
  |VAR(a)->[(ty,TEnv.find tenv a)]
  |ADD(a,b)->(ty,TyInt)::((gen_equations tenv a TyInt)@(gen_equations tenv b TyInt))
  |SUB(a,b)->(ty,TyInt)::((gen_equations tenv a TyInt)@(gen_equations tenv b TyInt))
  |MUL(a,b)->(ty,TyInt)::((gen_equations tenv a TyInt)@(gen_equations tenv b TyInt))
  |DIV(a,b)->(ty,TyInt)::((gen_equations tenv a TyInt)@(gen_equations tenv b TyInt))
  |EQUAL(a,b)->
    (
      let newt=fresh_tyvar() in
      (ref[]):=newt::!(ref[]);
      (ty,TyBool)::((gen_equations tenv a newt)@(gen_equations tenv b newt))
    )
  |LESS(a,b)->(ty,TyBool)::((gen_equations tenv a TyInt)@(gen_equations tenv b TyInt))
  |NOT(a)->(ty,TyBool)::(gen_equations tenv a TyBool)
  |NIL->
    (
      let newt=fresh_tyvar() in 
      [(ty,TyList(newt))]
    )
  |CONS(a,b)->
    (
      let newt=fresh_tyvar() in 
      (ty,TyList(newt))::((gen_equations tenv a newt)@(gen_equations tenv b (TyList(newt))))
    )
  |APPEND(a,b)->
    (
      let newt=fresh_tyvar() in 
      (ty,TyList(newt))::((gen_equations tenv a (TyList(newt)))@(gen_equations tenv b (TyList(newt))))
    )
  |HEAD(a)->
    (
      let newt=fresh_tyvar() in 
      (ty,newt)::(gen_equations tenv a (TyList(newt)))
    )
  |TAIL(a)->
    (
      let newt=fresh_tyvar() in 
      (ty,TyList(newt))::(gen_equations tenv a (TyList(newt)))
    )
  |ISNIL(a)->
    (
      let newt=fresh_tyvar() in 
      (ty,TyBool)::(gen_equations tenv a (TyList(newt)))
    )
  |IF(a,b,c)->
    (
      (gen_equations tenv a TyBool)@(gen_equations tenv b ty)@(gen_equations tenv c ty)
    )
  |LET(k,a,b)->
    (
      let newt=fresh_tyvar() in
      let newtenv=(TEnv.extend (k,newt) tenv) in
      (gen_equations tenv a newt)@(gen_equations newtenv b ty)
    )
  |LETREC(f,k,a,b)->
    (
      let newt=fresh_tyvar() in 
      let newt2=fresh_tyvar() in 
      let newtenv=TEnv.extend (k,newt) tenv in 
      let newtenv2=TEnv.extend (f,(TyFun(newt,newt2))) newtenv in 
      (gen_equations newtenv2 a newt)@(gen_equations newtenv2 b ty)
    )
  |LETMREC((f,k,a),(g,l,b),c)->
    (
      let newt=fresh_tyvar() in 
      let newt2=fresh_tyvar() in 
      let newt3=fresh_tyvar() in 
      let newt4=fresh_tyvar() in 
      let newtenv=TEnv.extend (k,newt) tenv in
      let newtenv2=TEnv.extend (f,TyFun(newt,newt2)) newtenv in
      let newtenv3=TEnv.extend (l,newt3) newtenv2 in
      let newtenv4=TEnv.extend (g,TyFun(newt3,newt4)) newtenv3 in
      (gen_equations tenv a newt2)@(gen_equations tenv b newt4)@(gen_equations newtenv4 c ty)

    )
  |PROC(k,a)->
    (
      let newt=fresh_tyvar() in 
      let newt2=fresh_tyvar() in 
      let newtenv=TEnv.extend (k,newt) tenv in 
      (ty,TyFun(newt,newt2))::(gen_equations (newtenv) a newt2)
    )
  |CALL(a,b)->
    (
      let newt=fresh_tyvar() in 
      (gen_equations tenv a (TyFun(newt,ty)))@(gen_equations tenv b newt)
    )
  |SEQ(a,b)->
    (
      let newt=fresh_tyvar() in 
      (gen_equations tenv a newt)@(gen_equations tenv b ty) 
    )

let rec checking
=fun a t->
  match t with
  |TyFun(t1,t2)->(checking a t1)||(checking a t2)
  |TyList(t)->(checking a t)
  |TyVar x->(a=x)
  |_->false

let rec unify
=fun t1 t2 subst->
  match (t1,t2) with
    |(TyUnit,TyUnit)->subst
    |(TyInt,TyInt)->subst
    |(TyBool,TyBool)->subst
    |(TyFun(a1,a2),TyFun(b1,b2))->
      (
        let newsubst=unify a1 b1 subst in
        let a3=Subst.apply a2 newsubst in 
        let b3=Subst.apply b2 newsubst in 
        unify a3 b3 newsubst
      )
    |(TyList(a),TyList(b))->
      (
        unify a b subst
      )
    |(TyVar(a),TyVar(b))->
      (
        if a=b then subst else Subst.extend a (TyVar(b)) subst
      )
    |(TyVar(a),b)->
      (
        if checking a b then raise(TypeError) else Subst.extend a b subst
      )
    |(a,TyVar(b))->
      (
        unify t2 t1 subst
      )
    |_->raise(TypeError)


let rec unifyall
=fun tyeqn subst->
  match tyeqn with
    |(a,b)::tl->
      (
        let newt=Subst.apply a subst in 
        let newt2=Subst.apply b subst in
        let newsubst= unify newt newt2 subst in 
        unifyall tl newsubst
      )
    |[]->subst

let solve
=fun eqn->
  unifyall eqn Subst.empty






let typeof : exp -> typ
=fun exp->
  let new_tv=fresh_tyvar () in 
  let eqns=gen_equations TEnv.empty exp new_tv in
  let subst=solve eqns in 
  let ty=Subst.apply new_tv subst in
  ty

(*
typeof(PROC("f",PROC("x",SUB(CALL(VAR "f",CONST 3),CALL(VAR "f",VAR "x")))))
typeof(PROC("f",CALL(VAR "f",CONST 11)))
typeof(LET("x",CONST 1,IF(VAR "x",SUB(VAR "x",CONST 1),CONST 0)))
//typeof(LETMREC(("even","x",IF(EQUAL(VAR "x",CONST 0),TRUE,CALL(VAR "odd",SUB(VAR "x",CONST 1)))),("odd","x",IF(EQUAL(VAR "x",CONST 0),FALSE,CALL(VAR "even",SUB(VAR "x",CONST 1)))),CALL (VAR "odd",CONST 13)))
typeof(LETREC ("reverse", "l",
     IF (ISNIL (VAR "l"), NIL,
      APPEND (CALL (VAR "reverse", TAIL (VAR "l")), CONS (HEAD (VAR "l"), NIL))),
     CALL (VAR "reverse", CONS (CONST 1, CONS (CONST 2, CONS (CONST 3, NIL)))))
)
typeof(LETREC ("reverse", "l",
     IF (ISNIL (VAR "l"), NIL,
      APPEND (CALL (VAR "reverse", TAIL (VAR "l")), CONS (HEAD (VAR "l"), NIL))),
     CALL (VAR "reverse",
      CONS (CONS (CONST 1, NIL),
       CONS (CONS (CONST 2, NIL), CONS (CONS (CONST 3, NIL), NIL)))))
)
//typeof(
       LETREC ("factorial", "x",
        IF (EQUAL (VAR "x", CONST 0), CONST 1,
         MUL (CALL (VAR "factorial", SUB (VAR "x", CONST 1)), VAR "x")),
        LETREC ("loop", "n",
         IF (EQUAL (VAR "n", CONST 0), UNIT,
          SEQ (PRINT (CALL (VAR "factorial", VAR "n")),
           CALL (VAR "loop", SUB (VAR "n", CONST 1)))),
CALL (VAR "loop", CONST 10))))
typeof(LET ("f", PROC("x", VAR "x"),
       IF(CALL (VAR "f", TRUE), CALL (VAR "f", CONST 1), CALL (VAR "f", CONST 2)))
)
typeof(LET ("fix",
        PROC ("f",
         CALL
          (PROC ("x",
            CALL (VAR "f", PROC ("y", CALL (CALL (VAR "x", VAR "x"), VAR "y")))),
          PROC ("x",
           CALL (VAR "f", PROC ("y", CALL (CALL (VAR "x", VAR "x"), VAR "y")))))),
        LET ("f",
         CALL (VAR "fix",
          PROC ("f",
           PROC ("x",
            IF (EQUAL (VAR "x", CONST 0), CONST 1,
             MUL (CALL (VAR "f", SUB (VAR "x", CONST 1)), VAR "x"))))),
         CALL (VAR "f", CONST 10))))
*)


(*

typeof(
       LETREC ("factorial", "x",
        IF (EQUAL (VAR "x", CONST 0), CONST 1,
         MUL (CALL (VAR "factorial", SUB (VAR "x", CONST 1)), VAR "x")),
        LETREC ("loop", "n",
         IF (EQUAL (VAR "n", CONST 0), UNIT,
          SEQ (PRINT (CALL (VAR "factorial", VAR "n")),
           CALL (VAR "loop", SUB (VAR "n", CONST 1)))),
CALL (VAR "loop", CONST 10))))  
-TyUnit 

typeof(LETMREC(("even","x",IF(EQUAL(VAR "x",CONST 0),TRUE,CALL
(VAR "odd",SUB(VAR "x",CONST 1)))),("odd","x",IF(EQUAL(VAR "x",CONST 0),FALSE,CALL
(VAR "even",SUB(VAR "x",CONST 1)))),CALL (VAR "odd",CONST 13)))
-TyBool
*)