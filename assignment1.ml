exception NotImplemented;;
let rec pascal : int * int -> int
= fun (n, m) -> 
    match m with
    |0->1
    |_->
    if n=m then 1
    else pascal(n-1,m)+pascal(n-1,m-1);;
let rec div
=fun a b->
  if b<2 then false
  else if (a mod b)=0 then true 
  else div a (b-1)
  
let prime : int -> bool
= fun n -> 
    match n with
    |1->false
    |2->true
    |_->if div n (n-1) then false else true

let rec range : int -> int -> int list
= fun n1 n2 ->
    if n1>n2 then []
    else n1::(range (n1+1) n2);; 

let rec sum
=fun l->
  match l with 
    |[]->0
    |hd::tl->hd+(sum tl)

let rec suml: int list list -> int
= fun l ->
    match l with
    |[]->0
    |hd::tl->(sum hd)+(suml tl)

(*[[1;2;3];[];[-1;5;2];[7]]*)
      
let rec reverse l=
    match l with
    |[]->[]
    |hd::tl->(reverse tl)@[hd];;
let rec fold_left f a l=
    match l with
    |[]->a
    |hd::tl->fold_left f (f a hd) tl;;
let rec int2string l=
  match l with
    |[]->""
    |hd::tl->(string_of_int hd)^(int2string tl)
let rec lst2int : int list -> int
= fun lst -> int_of_string(int2string lst)



let rec binarize : int -> int list
= fun n ->
    match n with
    |0->[0]
    |1->[1]
    |_->(binarize(n/2))@[n mod 2]

let rec max : int list -> int
= fun lst ->
    match lst with
     |[]->raise(Failure("empty list")) 
     |hd::[]->hd
     |hd::tl-> if hd>(max tl) then hd else (max tl)
    

let rec min : int list -> int
= fun lst ->
  match lst with
   |[]->raise(Failure("empty list")) 
   |hd::[]->hd
   |hd::tl-> if hd<(max tl) then hd else (max tl)

type btree = Empty | Node of int * btree * btree

let rec mem : int -> btree -> bool
= fun n t ->
    match t with  
      |Empty->false
      |Node(v,l,r)->
        if n=v then true else (mem n l)||(mem n r)


type btree = 
  | Leaf of int
  | Left of btree
  | Right of btree
  | LeftRight of btree * btree;;

let rec mirror : btree -> btree
= fun tree ->
    match tree with
      |Left(t)->Right(mirror t)
      |Right(t)->Left(mirror t)
      |LeftRight(l,r)->LeftRight(mirror r,mirror l)
      |Leaf n->Leaf n
      




type nat = ZERO | SUCC of nat;;

let rec natadd : nat -> nat -> nat
= fun n1 n2 ->
    match n1 with
      |ZERO->n2
      |SUCC(a)->natadd a (SUCC n2)


let rec natmul : nat -> nat -> nat
= fun n1 n2 ->
    match n1 with
      |ZERO->ZERO
      |SUCC(a)-> natadd (natmul a n2) n2

type formula = 
  | True
  | False
  | Not of formula
  | AndAlso of formula * formula
  | OrElse of formula * formula
  | Imply of formula * formula
  | Equal of exp * exp

and exp = 
  | Num of int
  | Plus of exp * exp
  | Minus of exp * exp;;


let rec npm
=fun a->
    match a with 
    |Num(n)->n
    |Plus(m,n)->npm(m)+npm(n)
    |Minus(m,n)->npm(m)-npm(n)
  
let rec eval : formula -> bool
= fun f ->
    match f with
      |True->true
      |False->false
      |Not(a)->not (eval a)
      |AndAlso(a,b)-> (eval a)&&(eval b)
      |OrElse(a,b)-> (eval a)||(eval b)
      |Imply(a,b)->
        if not (eval a) then true
        else if (eval b) then true
        else false
      |Equal(a,b)-> npm(a)=npm(b)

type mobile = branch * branch
and branch =
  | SimpleBranch of length * weight
  | CompoundBranch of length * mobile
and length = int
and weight = int;;



let left m=
        match m with
          |(a,b)->a
let right m=
        match m with
          |(a,b)->b
let rec lengthsum branch=
        match branch with
          |SimpleBranch(a,b)->a
          |CompoundBranch(c,d)->(lengthsum (left d)+(lengthsum (right d)))

let rec weightsum branch=
        match branch with 
          |SimpleBranch(a,b)->b
          |CompoundBranch(c,d)->(weightsum (left d))+(weightsum (right d))

let isSimple branch=
        match branch with 
          |SimpleBranch(a,b)->true
          |CompoundBranch(c,d)->false
let isCom branch=
      match branch with 
        |SimpleBranch(a,b)->false
        |CompoundBranch(c,d)->true
let isBalance m=
        match m with
          |(a,b)->((lengthsum a)*(weightsum a))=((lengthsum b)*(weightsum b))
let rec branchBalance branch=
        match branch with
          |SimpleBranch(a,b)->true
          |CompoundBranch(c,d)->((isBalance d)&&(branchBalance (left d))&&(branchBalance (right d)))

let rec balanced: mobile -> bool
= fun mobile ->
    match mobile with 
      |(a,b)->(branchBalance a)&&(branchBalance b)
      



 

(*
(CompoundBranch(3,
(CompoundBranch(2,(SimpleBranch(1,3),SimpleBranch(2,1))),
SimpleBranch(1,4))),
SimpleBranch(6,4))
*)
(*
(CompoundBranch(3,
(CompoundBranch(2,(SimpleBranch(1,1),SimpleBranch(2,1))),
SimpleBranch(1,4))),
SimpleBranch(6,3))
*)