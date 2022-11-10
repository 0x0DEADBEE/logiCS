include "basics/logic.ma".
include "arithmetics/nat.ma".
include "basics/lists/list.ma".

axiom true_or_false: ∀b. b = true ∨ b = false.

(*let rec leq_nat n m on n ≝
  match n with
  [
  O ⇒ True
  | S x ⇒ (S x) ≤ m
  ]. *)
 inductive mylist_nat : Type[0] ≝
  | Nil : mylist_nat
  | Cons : nat → mylist_nat → mylist_nat.
  
 
let rec insert_ordered n l on l:mylist_nat ≝
  match l with
  [ Nil ⇒ Cons n Nil
  | Cons head tail ⇒
  if (leb n head) then (Cons n (Cons head tail))
  else (Cons head (insert_ordered n tail))
  ].
  
let rec sort l on l:mylist_nat ≝
  match l with
  [Nil ⇒ Nil
  | Cons head tail ⇒ insert_ordered head (sort tail)].

let rec inside x l on l ≝
  match l with
  [Nil ⇒ False
  | Cons head tail => head = x ∨ (inside x tail)].
 
theorem equal_already_inside : ∀x,y,l. ((inside x (insert_ordered y l)) →  ((x = y) ∨ (inside x l))).
  assume x:nat
  assume y:nat
  assume l:mylist_nat
  we proceed by induction on l to prove ((inside x (insert_ordered y l)) →  ((x = y) ∨ (inside x l)))
  case Nil
    we need to prove ((inside x (insert_ordered y Nil)) →  ((x = y) ∨ (inside x Nil)))
    that is equivalent to ((inside x (Cons y Nil)) →  ((x = y) ∨ (False)))
    that is equivalent to ((y=x ∨ (inside x Nil)) →  ((x = y) ∨ (False)))
    that is equivalent to ((y=x ∨ False) →  ((x = y) ∨ (False)))
    suppose (y=x ∨ False) (H1)
    we proceed by cases on H1 to prove ((x = y) ∨ False)
    case or_introl
      suppose (y=x) (H2)
      we need to prove (x=y∨False)
      by H2, or_introl done
    case or_intror
      suppose False (abs)
      done
  case Cons (head:nat) (tail:mylist_nat)
    by induction hypothesis we know ((inside x (insert_ordered y tail)) →  ((x = y) ∨ (inside x tail))) (IH1)
    we need to prove (inside x (insert_ordered y (Cons head tail))→x=y∨inside x (Cons head tail))
    that is equivalent to (inside x (
    if (leb y head) then (Cons y (Cons head tail))
    else (Cons head (insert_ordered y tail)))→x=y∨inside x (Cons head tail))
    that is equivalent to  (inside x
    (if (leb y head) then (Cons y (Cons head tail)) 
    else (Cons head (insert_ordered y tail)) ) →x=y∨ (head=x ∨ (inside x tail)))
    by true_or_false we proved
      (leb y head = true ∨
    leb y head = false) (TF)
    we proceed by cases on TF to prove (inside x
  (if leb y head 
   then Cons y (Cons head tail) 
   else Cons head (insert_ordered y tail) )
  →x=y∨(head=x∨inside x tail))
  
    case or_introl
      suppose (leb y head = true) (H2)
      we need to prove (inside x
    (if (leb y head) then (Cons y (Cons head tail)) 
    else (Cons head (insert_ordered y tail)) ) →x=y∨ (head=x ∨ (inside x tail)))
    (*that is equivalent to (inside x (Cons y (Cons head tail)) →x=y∨ (head=x ∨ (inside x tail))))*)
    

    case or_intror
    
    
    
  