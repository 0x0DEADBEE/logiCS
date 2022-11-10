include "basics/logic.ma".
include "basics/core_notation.ma".
include "arithmetics/nat.ma".

axiom and_true : ∀x,y : bool. ((x∧y)=true) → (x=true)∧(y=true).
lemma true_or_false: ∀b: bool. b = true ∨ b = false.
 //
qed.


inductive list : Type[0] ≝
  | nil : list
  | cons : ℕ → list → list.
let rec smallereq x L on L ≝
  match L with
  [ nil ⇒ true
  | cons head tail ⇒ leb x head ].
let rec sorted L on L ≝
  match L with
  [ nil ⇒ true
  | cons head tail ⇒  ((sorted tail) ∧ smallereq head tail) ].
  
let rec insert x L on L ≝
  match L with
  [ nil ⇒ cons x nil  
  | cons head tail ⇒
    if (leb x head) then (cons x (cons head L))
    else (cons head (insert x tail))].

axiom l1 : ∀x,y,l. (x≤ y ∧ (smallereq y l = true) → smallereq x (insert y l) = true).
axiom l2 : ∀x,y,l. (leb x y = false) ∧ (smallereq y l = true) → (smallereq y (insert x l) = true).

theorem th1 : ∀x,l. sorted l = true → sorted (insert x l) = true.
  assume x: ℕ
  assume l: list
  we proceed by induction on l to prove ((sorted l = true) → sorted (insert x l) = true)
  case nil
    we need to prove ((sorted nil = true) → sorted (insert x nil) = true)
    that is equivalent to ((true = true) → sorted (cons x nil) = true)
    that is equivalent to ((true = true) → ((smallereq x nil) ∧ sorted nil) = true)
    that is equivalent to ((true = true) → (true ∧ true) = true)
    that is equivalent to ((true = true) → true = true)
    done
  case cons (head: ℕ) (tail:list)
    by induction hypothesis we know ((sorted tail = true) → sorted (insert x tail) = true) (II)
    we need to prove  (sorted (cons head tail)=true→sorted (insert x (cons head tail))=true)
    that is equivalent to ((sorted tail ∧ (smallereq head tail))=true→sorted (insert x (cons head tail))=true)
    that is equivalent to ((sorted tail ∧ (smallereq head tail))=true→
    (sorted (if (leb x head) then (cons x (cons head (cons head tail)))
            else (cons head (insert x tail)))=true))
     suppose ((sorted tail∧smallereq head tail)=true) (H1)
     by H1, and_true we proved ((sorted tail = true) ∧ (smallereq head tail = true)) (H2)
     by H2 we have (sorted tail = true) (H4) and (smallereq head tail = true) (H5)
     by true_or_false we proved ((leb x head) = true ∨ (leb x head) = false) (TF)
     we proceed by cases on TF to prove  (sorted
  (if leb x head 
   then cons x (cons head (cons head tail)) 
   else cons head (insert x tail) )
  =true)
    case or_introl
      suppose ((leb x head) = true) (H6)
      we proved (leb x head) (H7)
      we need to prove  (sorted (cons x (cons head (cons head tail))) =true)
    case or_intror
     
     
     
     
     
     
     
     
     