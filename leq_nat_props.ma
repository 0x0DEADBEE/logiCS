include "basics/logic.ma".
include "arithmetics/nat.ma".
let rec leq_nat n m on n ≝
  match n with
  [
  O ⇒ True
  | S x ⇒ (S x) ≤ m
  ].
 
 
let rec concat l1 l2 on l1 ≝ 
  match l1 with
  [
  Nil ⇒ l2
  | Cons head tail ⇒ Cons head(concat tail l2)
  ].

(*assuming all elements differ from each other*)
let rec _ordered_insert n l acc on l ≝
  match l with
  [ Nil ⇒ concat acc (Cons n Nil)
  | Cons head tail ⇒ 
  (_ordered_insert n tail)
  ].