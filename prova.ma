include "basics/logic.ma".
include "arithmetics/nat.ma".
include "basics/bool.ma".
include "basics/core_notation.ma".
lemma true_or_false: ∀b: bool. b = true ∨ b = false.
 //
qed.


let rec leqb n m on n :=
 match n with
 [ O => true
 | S x =>
    match m with
    [ O => false
    | S y => leqb x y
    ]
 ].

inductive list_nat : Type[0] ≝
  | Nil : list_nat
  | Cons : ℕ → list_nat → list_nat.

let rec insert n L on L ≝
  match L with
  [ Nil ⇒ Cons n Nil
  | Cons head tail ⇒
    if (leqb n head) then (Cons n (Cons head tail))
    else (Cons head (insert n tail))].
let rec sort L on L ≝
  match L with
  [ Nil ⇒ Nil
  | Cons head tail ⇒ insert head (sort tail)].

(*Capital False & x=y are bools*)
let rec belong n L on L ≝
  match L with
  [ Nil ⇒ False
  | Cons head tail ⇒ (head=n)∨(belong n tail)].
  
(*dimostrate che X appartiene all'inserimento di Y nella lista ordinata
         L sse X è uguale a Y oppure appartiene a L*)
theorem b : ∀X,Y,L. ((belong X (insert Y L)) →  ((X=Y)∨(belong X L))).
  assume X:ℕ 
  assume Y:ℕ
  assume L:list_nat
  we proceed by induction on L to prove  (belong X (insert Y L)→X=Y∨belong X L)
  case Nil
    we need to prove  (belong X (insert Y Nil)→X=Y∨belong X Nil)
    that is equivalent to (belong X (Cons Y Nil) → (X=Y)∨False)
    that is equivalent to  ((Y=X)∨(belong X Nil)→ (X=Y)∨False)
    that is equivalent to  (Y=X∨False →X=Y∨False)
    suppose (Y=X∨False) (H1)
    we proceed by cases on H1 to prove  (X=Y∨False)
    case or_introl
      suppose (Y=X) (H2)
      by H2, or_introl done
    case or_intror
      suppose False (abs)
      done

  case Cons (H:ℕ) (T:list_nat)
  by induction hypothesis we know ((belong X (insert Y T)) →  ((X=Y)∨(belong X T))) (II)
  we need to prove  (belong X (insert Y (Cons H T))→X=Y∨belong X (Cons H T))
  that is equivalent to (belong X (
    if (leqb Y H) then (Cons Y (Cons H T))
    else (Cons H (insert Y T))
  ) → X=Y∨((H=X)∨(belong X T)))
  by true_or_false we proved (leqb Y H = true ∨ leqb Y H = false) (TF)
  we proceed by cases on TF to prove  (belong X (if leqb Y H then Cons Y (Cons H T) else Cons H (insert Y T) )
  →X=Y∨(H=X∨belong X T))
  case or_introl
    we need to prove (belong X (Cons Y (Cons H T) ) →X=Y∨(H=X∨belong X T))
  
  
  
  
  
  
  
  
  
  
  
  