type exp =
  | NUM of int | TRUE | FALSE | UNIT
  | VAR of id
  | ADD of exp * exp
  | SUB of exp * exp
  | MUL of exp * exp
  | DIV of exp * exp
  | EQUAL of exp * exp
  | LESS of exp * exp
  | NOT of exp
  | SEQ of exp * exp                 (* sequence *)
  | IF of exp * exp * exp            (* if-then-else *)
  | WHILE of exp * exp               (* while loop *)
  | LETV of id * exp * exp           (* variable binding *)
  | LETF of id * id list * exp * exp (* procedure binding *)
  | CALLV of id * exp list           (* call by value *)
  | CALLR of id * id list            (* call by referenece *)
  | RECORD of (id * exp) list        (* record construction *)
  | FIELD of exp * id                (* access record field *)
  | ASSIGN of id * exp               (* assgin to variable *)
  | ASSIGNF of exp * id * exp        (* assign to record field *)
  | WRITE of exp
and id = string

type loc = int
type value =
| Num of int
| Bool of bool
| Unit
| Record of record 
and record = (id * loc) list
type memory = (loc * value) list
type env = binding list
and binding = LocBind of id * loc | ProcBind of id * proc
and proc = id list * exp * env

(********************************)
(*     Handling environment     *)
(********************************)

let rec lookup_loc_env : id -> env -> loc
= fun x env ->
  match env with
  | [] -> raise(Failure ("Variable "^x^" is not included in environment"))
  | hd::tl ->
    begin match hd with
    | LocBind (id,l) -> if(x=id) then l else lookup_loc_env x tl
    | ProcBind _ -> lookup_loc_env x tl
    end

let rec lookup_proc_env : id -> env -> proc
= fun x env ->
  match env with
  | [] -> raise(Failure ("Variable "^x^" is not included in environment"))
  | hd::tl ->
    begin match hd with
    | LocBind _ -> lookup_proc_env x tl
    | ProcBind (id,binding) -> if (x=id) then binding else lookup_proc_env x tl
    end

let extend_env : binding -> env -> env
= fun e env -> e::env

let empty_env = []


(***************************)
(*     Handling memory     *)
(***************************)

let rec lookup_mem : loc -> memory -> value
= fun l mem ->
  match mem with
  | [] -> raise(Failure ("location "^(string_of_int l)^" is not included in memory"))
  | (loc,v)::tl -> if(l=loc) then v else lookup_mem l tl

let extend_mem : (loc * value) -> memory -> memory
= fun (l,v) mem -> (l,v)::mem

let empty_mem = []

(***************************)
(*     Handling record     *)
(***************************)

let rec lookup_record : id -> record -> loc
= fun id record -> 
  match record with
    | [] -> raise(Failure ("field "^ id ^" is not included in record"))
    | (x,l)::tl -> if(id=x) then l else lookup_record id tl


let extend_record : (id * loc) -> record -> record
= fun (x,l) record -> (x,l)::record

let empty_record = []

(***************************)

let counter = ref 0
let new_location () = counter:=!counter+1;!counter

exception NotImplemented
exception UndefinedSemantics

let rec list_fold2 : ('a -> 'b -> 'c -> 'c)-> 'a list -> 'b list -> 'c -> 'c
= fun func l1 l2 acc ->
  match (l1,l2) with
  | ([],[]) -> acc
  | (hd1::tl1,hd2::tl2) -> list_fold2 func tl1 tl2 (func hd1 hd2 acc)
  | _ -> raise (Failure "two lists have different length")

let rec list_fold : ('a -> 'b -> 'b) -> 'a list -> 'b -> 'b
= fun func l acc ->
  match l with
  | [] -> acc
  | hd::tl -> list_fold func tl (func hd acc)

let value2str : value -> string
= fun v ->
  match v with
  | Num n -> string_of_int n
  | Bool b -> string_of_bool b
  | Unit -> "unit"
  | Record _ -> "record" 

let rec eval_aop : env -> memory -> exp -> exp -> (int -> int -> int) -> (value * memory)
= fun env mem e1 e2 op ->
  let (v1,mem1) = eval env mem e1 in
  let (v2,mem2) = eval env mem1 e2 in
  match (v1,v2) with
  | (Num n1, Num n2) -> (Num (op n1 n2), mem2)
  | _ -> raise (Failure "arithmetic operation type error")

and eval : env -> memory -> exp -> (value * memory) 
=fun env mem e -> 
  match e with
  | WRITE e -> 
    let (v1,mem1) = eval env mem e in
    let _ = print_endline(value2str v1) in
    (v1,mem1)
  |NUM(n)->(Num(n),mem)
  |TRUE->(Bool(true),mem)
  |FALSE->(Bool(false),mem)
  |UNIT->(Unit,mem)
  |VAR(a)->((lookup_mem (lookup_loc_env a env) mem),mem)
  |ADD(a,b)->
    (
      let (v1,mem2)= eval env mem a in
      let (v2,mem3)= eval env mem2 b in
      match v1,v2 with
        |Num(n1), Num(n2)->(Num(n1+n2),mem3)
        |_,_->raise(UndefinedSemantics)
    )
  |SUB(a,b)->
    (
      let (v1,mem2)= eval env mem a in
      let (v2,mem3)= eval env mem2 b in
      match v1,v2 with
        |Num(n1), Num(n2)->(Num(n1-n2),mem3)
        |_,_->raise(UndefinedSemantics)
    )
  |MUL(a,b)->
    (
      let (v1,mem2)= eval env mem a in
      let (v2,mem3)= eval env mem2 b in
      match v1,v2 with
        |Num(n1), Num(n2)->(Num(n1*n2),mem3)
        |_,_->raise(UndefinedSemantics)
    )
  |DIV(a,b)->
    (
      let (v1,mem2)= eval env mem a in
      let (v2,mem3)= eval env mem2 b in
      match v1,v2 with
        |Num(n1), Num(0)->raise(UndefinedSemantics)
        |Num(n1), Num(n2)->(Num(n1/n2),mem3)
        |_,_->raise(UndefinedSemantics)
    )
  |EQUAL(a,b)->
    (
      let (v1,mem2)= eval env mem a in
      let (v2,mem3)= eval env mem2 b in
      match v1,v2 with
        |Num(n1), Num(n2)->if n1=n2 then (Bool(true),mem3) else (Bool(false),mem3)
        |Bool(n1), Bool(n2)->if n1=n2 then (Bool(true),mem3) else (Bool(false),mem3)
        |Unit,Unit->(Bool(true),mem3)
        |_,_->raise(UndefinedSemantics)
    )
  |LESS(a,b)->
    (
      let (v1,mem2)= eval env mem a in
      let (v2,mem3)= eval env mem2 b in
      match v1,v2 with
        |Num(n1), Num(n2)->if n1<n2 then (Bool(true),mem3) else (Bool(false),mem3)
        |_,_->raise(UndefinedSemantics)
    )
  |NOT(a)->
    (
      let (v,mem2)= eval env mem a in
      match v with
        |Bool(n)->if n=true then (Bool(false),mem2) else (Bool(true),mem2)
        |_->raise(UndefinedSemantics)
    )
  |SEQ(a,b)->
    (
      let (v,mem2)= eval env mem a in
      eval env mem2 b
    )
  |IF(a,b,c)->
    (
      let (v,mem2)= eval env mem a in
      match v with
        |Bool(n1)->if n1 then (eval env mem2 b) else (eval env mem2 c)
        |_->raise(UndefinedSemantics)
    )
  |WHILE(a,b)->
    (
      let (v1,mem2)= eval env mem a in 
      match v1 with
        |Bool(true)->
          (
            let (v2,mem3)=eval env mem2 b in
            eval env mem3 (WHILE(a,b))
          )
        |Bool(false)->(Unit,mem2)
        |_->raise(UndefinedSemantics)
    )
  |LETV(k,a,b)->
    (
      let (v1,mem2)=eval env mem a in
      let newloc=new_location() in
      let (v2,mem3)=eval (extend_env (LocBind (k,newloc)) env) (extend_mem(newloc,v1) mem2) b in 
      (v2,mem3)
    )
  |LETF(fx,k,a,b)->
    (
      let (v1,mem2)=eval (extend_env (ProcBind(fx,(k,a,env))) env) mem b in 
      (v1,mem2)
    )
  |FIELD(a,k)->
    (
      let (v1,mem2)=eval env mem a in
      match v1 with
        |Record(r)->(lookup_mem (lookup_record k r) mem, mem2)
        |_->raise(UndefinedSemantics)
    )
  |ASSIGN(k,a)->
    (
      let (v,mem2)= eval env mem a in
      (v, extend_mem((lookup_loc_env k env),v) mem2)
    )
  |ASSIGNF(a,k,b)->
    (
      let (v1,mem2)=eval env mem a in 
      let (v2,mem3)=eval env mem2 b in
        match v1 with 
        |Record(r)->(v2,extend_mem(lookup_record k r, v2) mem3)
        |_->raise(UndefinedSemantics)
    )

  | _ -> raise NotImplemented (* TODO *)

let runb : exp -> value 
=fun exp -> let (v, _) = eval empty_env empty_mem exp in v;;

