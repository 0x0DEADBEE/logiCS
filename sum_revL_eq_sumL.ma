include "basics/logic.ma".
(*
include "basics/lists/list.ma".
include "arithmetics/nat.ma".
include "basics/core_notation.ma".
*)

inductive nat : Type[0] ≝
  O : nat
  | S : nat → nat.
  
  
inductive list_nat : Type[0] ≝
  | Nil : list_nat
  | Cons : nat → list_nat → list_nat.
  
 let rec plus n m on n ≝
  match n with
  [ O ⇒ m
  | S x ⇒ S (plus x m) ].

  
let rec sumL L on L ≝
  match L with
  [ Nil ⇒ O
  | Cons head tail ⇒ plus head (sumL tail)
  ].
  
(*insert list upon an element*)
let rec insertL L e on L ≝
  match L with
  [ Nil ⇒ Cons e Nil
  | Cons head tail ⇒ Cons head (insertL tail e)
  ].
  
let rec my_revL L on L ≝
  match L with
  [ Nil ⇒ Nil
  | Cons head tail ⇒ insertL (my_revL tail) head
  ].

let rec insertAtBottomL L e on L ≝
  match L with
  [ Nil ⇒ Cons e Nil
  | Cons head tail ⇒ Cons head (insertAtBottomL tail e)
  ].

let rec rev L on L ≝
  match L with
  [ Nil ⇒ Nil
  | Cons head tail ⇒ insertAtBottomL (rev tail) head
  ].
  
lemma plus_O : ∀head. (plus head O = head).
  assume head : nat
  we need to prove (plus head O = head)
  we proceed by induction on head to prove (plus head O = head)
  case O
    we need to prove (plus O O = O)
    done
  case S (x:nat)
    by induction hypothesis we know (plus x O = x) (IH1)
    we need to prove (plus (S x) O = S x)
    that is equivalent to (S (plus x O) = S x)
    by IH1 done
  qed.
    

theorem if_both_zero : ∀l1,l2,head. ((sumL l1 = sumL l2) ∧ (sumL l1 = O)) → (plus head (sumL l2) = head).
  assume l1: list_nat
  assume l2: list_nat
  assume head: nat
  suppose ((sumL l1 = sumL l2) ∧ (sumL l1 = O)) (H1)
  by H1 we have (sumL l1 = sumL l2) (H2) and (sumL l1 = O) (H3)
  by H2, H3 we proved (sumL l2 = O) (H4)
  we need to prove (plus head (sumL l2)=head)
  by H4, plus_O done
 qed.
    

  
theorem if_eq_then : ∀l1,l2,head. (sumL l1 = sumL l2) → (sumL (insertAtBottomL l1 head) = plus head (sumL l2)).
  assume l1: list_nat
  assume l2: list_nat
  assume head : nat
  suppose (sumL l1 = sumL l2) (H1)
  we need to prove (sumL (insertAtBottomL l1 head) = plus head (sumL l2))
  we proceed by induction on l1 to prove (sumL (insertAtBottomL l1 head) = plus head (sumL l2))
  case Nil
    we need to prove (sumL (insertAtBottomL Nil head) = plus head (sumL l2))
    that is equivalent to (sumL (Cons head Nil) = plus head (sumL l2))
    that is equivalent to (plus head (sumL Nil) = plus head (sumL l2))
    that is equivalent to (plus head O = plus head (sumL l2))
    suppose (l1 = Nil) (H2)
    by H1,if_both_zero done
  case Cons hd tail
  
theorem sum_L_revL_eq : ∀L. sumL(rev L) = sumL L.
  assume L : list_nat
  we proceed by induction on L to prove (sumL(rev L) = sumL L)
  case Nil
    we need to prove (sumL(rev Nil) = sumL Nil)
    that is equivalent to (sumL Nil = sumL Nil)
    done
  case Cons (head : nat) (tail : list_nat)
    by induction hypothesis we know (sumL(rev tail) = sumL tail) (IH1)
    we need to prove (sumL(rev (Cons head tail)) = sumL (Cons head tail))
    that is equivalent to (sumL(rev (Cons head tail)) = sumL (Cons head tail))
    that is equivalent to (sumL (insertAtBottomL (rev tail) head) = plus head (sumL tail))
    
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  

