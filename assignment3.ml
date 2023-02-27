type program = exp
and exp = 
  | UNIT
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

type value = 
  | Unit 
  | Int of int 
  | Bool of bool 
  | List of value list
  | Procedure of var * exp * env 
  | RecProcedure of var * var * exp * env
  | MRecProcedure of var * var * exp *
                     var * var * exp * env
and env = (var * value) list

let rec fold_left : ('a -> 'b -> 'a) -> 'a -> 'b list -> 'a
= fun f accu lst ->
  match lst with
  | [] -> accu
  | hd::tl -> fold_left f (f accu hd) tl

let rec map : ('a -> 'b) -> 'a list -> 'b list
= fun f lst ->
  match lst with
  | [] -> []
  | hd::tl -> (f hd)::(map f tl)

let rec string_of_value v = 
  match v with
  | Int n -> string_of_int n
  | Bool b -> string_of_bool b
  | List lst -> "[" ^ fold_left (fun s x -> s ^ ", " ^ x) "" (map string_of_value lst) ^ "]"
  | _ -> "(functional value)"

exception UndefinedSemantics

let empty_env = []
let extend_env (x,v) e = (x,v)::e
let rec lookup_env x e = 
  match e with
  | [] -> raise (Failure ("variable " ^ x ^ " is not bound in env")) 
  | (y,v)::tl -> if x = y then v else lookup_env x tl

let rec eval : exp -> env -> value
=fun exp env ->
  match exp with
  |PRINT e -> (print_endline (string_of_value (eval e env)); Unit)
  |UNIT->Unit
  |TRUE->Bool(true)
  |FALSE->Bool(false)
  |CONST(a)->Int(a)
  |VAR(a)->(lookup_env a env)
  |ADD(a,b)->
    (
      let v1= eval a env in
      let v2= eval b env in
      match v1,v2 with
        |Int(n1), Int(n2)->Int(n1+n2)
        |_,_->raise(UndefinedSemantics)
    )
  |SUB(a,b)->
    (
      let v1= eval a env in
      let v2= eval b env in
      match v1,v2 with
        |Int(n1), Int(n2)->Int(n1-n2)
        |_,_->raise(UndefinedSemantics)
    )
  |MUL(a,b)->
    (
      let v1= eval a env in
      let v2= eval b env in
      match v1,v2 with
        |Int(n1), Int(n2)->Int(n1*n2)
        |_,_->raise(UndefinedSemantics)
    )
  |DIV(a,b)->
    (
      let v1= eval a env in
      let v2= eval b env in
      match v1,v2 with
        |Int(n1), Int(0)->raise(UndefinedSemantics)
        |Int(n1), Int(n2)->Int(n1/n2)
        |_,_->raise(UndefinedSemantics)
    )
  |EQUAL(a,b)->
    (
      let v1= eval a env in
      let v2= eval b env in
      match v1,v2 with
        |Int(n1), Int(n2)->if n1=n2 then Bool(true) else Bool(false)
        |Bool(n1),Bool(n2)->if n1=n2 then Bool(true) else Bool(false)
        |_,_->raise(UndefinedSemantics)
    )
    
  |LESS(a,b)->
    (
      let v1= eval a env in
      let v2= eval b env in
      match v1,v2 with
        |Int(n1), Int(n2)->if n1<n2 then Bool(true) else Bool(false)
        |_,_->raise(UndefinedSemantics)
    )
  |NOT(a)->
    (
      let v= eval a env in
      match v with
        |Bool(n1)->if n1=true then Bool(false) else Bool(true)
        |_->raise(UndefinedSemantics)
    )
  |NIL->List([])
  |CONS(a,b)->
    (
      let v1= eval a env in
      let v2= eval b env in
      match v1,v2 with
        |v1, List(n2)->List(v1::n2)
        |_,_->raise(UndefinedSemantics)
    )
  |APPEND(a,b)->
    (
      let v1= eval a env in
      let v2= eval b env in
      match v1,v2 with
        |List(n1), List(n2)->List(n1@n2)
        |_,_->raise(UndefinedSemantics)
    )
  |HEAD(a)->
    (
      let v= eval a env in
      match v with
        |List(hd::tl)->hd
        |_->raise(UndefinedSemantics)
    )
  |TAIL(a)->
    (
      let v= eval a env in
      match v with
        |List(hd::tl)->List(tl)
        |_->raise(UndefinedSemantics)
    )
  |ISNIL(a)->
    (
      let v= eval a env in
      match v with
        |List(k)->if (k=[]) then Bool(true) else Bool(false)
        |_->raise(UndefinedSemantics)
    )
  |IF(a,b,c)->
    (
      let v= eval a env in
      match v with
        |Bool(n1)->if n1 then (eval b env) else (eval c env)
        |_->raise(UndefinedSemantics)
    )
  |LET(k,a,b)->
    (
      let x= eval a env in 
      eval b (extend_env (k,x) env)
    )
  |LETREC(f,k,a,b)->
    (
      let fx=RecProcedure(f,k,a,env) in 
      eval b (extend_env (f,fx) env)
    )
  |LETMREC((f,k,a),(g,l,b),c)->
    (
      let fx=MRecProcedure(f,k,a,g,l,b,env) in
      let gx=MRecProcedure(g,l,b,f,k,a,env) in
      eval c (extend_env (g,gx) (extend_env (f,fx) env))
    )
  |PROC(k,a)->
    (
      Procedure(k,a,env)
    )
  |CALL(a,b)->
    (
      let v1= eval a env in
      let v2= eval b env in
      match v1 with
        |Procedure(k,a2,env2)->eval a2 (extend_env (k,v2) env2)
        |RecProcedure(f,k,a2,env2)->eval a2 (extend_env (k,v2) (extend_env (f,v1) env2))
        |MRecProcedure(f,k,a2,g,l,b2,env2)->eval a2 (extend_env (g,v1) (extend_env (f,v1) (extend_env (k,v2) env2)))
        |_->raise(UndefinedSemantics)
    )
  |SEQ(a,b)->
    (
      let v= eval a env in
      eval b env
    )
  | _ -> raise (Failure "Not implemented")


let runml : program -> value
=fun pgm -> eval pgm empty_env
 

let ex1 = LET ("x", CONST 1,
LET ("f", PROC ("y", ADD (VAR "x", VAR "y")),
LET ("x", CONST 2,
LET ("g", PROC ("y", ADD (VAR "x", VAR "y")),
ADD (CALL (VAR "f", CONST 1), CALL (VAR "g", CONST 1))))));;

let ex2 = LETREC ("double", "x",
IF (EQUAL (VAR "x", CONST 0), CONST 0,
ADD (CALL (VAR "double", SUB (VAR "x", CONST 1)), CONST 2)),
CALL (VAR "double", CONST 6));;

let ex3 = LETMREC
(("even", "x",
IF (EQUAL (VAR "x", CONST 0), TRUE,
CALL (VAR "odd", SUB (VAR "x", CONST 1)))),
("odd", "x",
IF (EQUAL (VAR "x", CONST 0), FALSE,
CALL (VAR "even", SUB (VAR "x", CONST 1)))),
CALL (VAR "odd", CONST 13));;

let ex4 = LETREC ("factorial", "x",
IF (EQUAL (VAR "x", CONST 0), CONST 1,
MUL (CALL (VAR "factorial", SUB (VAR "x", CONST 1)), VAR "x")),
LETREC ("loop", "n",
IF (EQUAL (VAR "n", CONST 0), UNIT,
SEQ (PRINT (CALL (VAR "factorial", VAR "n")),
CALL (VAR "loop", SUB (VAR "n", CONST 1)))),
CALL (VAR "loop", CONST 10)));;

let ex5 = LETREC ("range", "n",
IF (EQUAL (VAR "n", CONST 1), CONS (CONST 1, NIL),
CONS (VAR "n", CALL (VAR "range", SUB (VAR "n", CONST 1)))),
CALL (VAR "range", CONST 10));;

let ex6 = LETREC ("reverse", "l",
IF (ISNIL (VAR "l"), NIL,
APPEND (CALL (VAR "reverse", TAIL (VAR "l")), CONS (HEAD (VAR "l"), NIL))),
CALL (VAR "reverse", CONS (CONST 1, CONS (CONST 2, CONS (CONST 3, NIL)))));;

let ex7 = LET ("fix",
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
CALL (VAR "f", CONST 10)));;

let ex8 = LET ("fix",
PROC ("f",
CALL
(PROC ("x",
CALL (VAR "f", PROC ("y", CALL (CALL (VAR "x", VAR "x"), VAR "y")))),
PROC ("x",
CALL (VAR "f", PROC ("y", CALL (CALL (VAR "x", VAR "x"), VAR "y")))))),
LET ("f",
CALL (VAR "fix",
PROC ("range",
PROC ("n",
IF (EQUAL (VAR "n", CONST 1), CONS (CONST 1, NIL),
CONS (VAR "n", CALL (VAR "range", SUB (VAR "n", CONST 1))))))),
CALL (VAR "f", CONST 10)));;

(*ex 6 이랑 ex 3 고치기!!*)