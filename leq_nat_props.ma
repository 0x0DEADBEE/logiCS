include "basics/logic.ma".
inductive nat : Type[0] ≝
  O : nat
  | S : nat → nat.
inductive list_nat : Type[0] ≝
  Nil : list_nat
  | Cons : nat → list_nat → list_nat.
  
let rec leq_nat n m on n ≝
  match n with
  [ O ⇒ True
  | S x ⇒ leq_nat x m
  ].