include "basics/logic.ma".
include "basics/lists/list.ma".
include "arithmetics/nat.ma".
include "basics/core_notation.ma".
(*remember the dot after the lemma declaration*)
inductive nat : Type[0] ≝
  O : nat
  | S : nat → nat.

let rec plus n m on n ≝
  match n with
  [ O ⇒ m
  | S x ⇒ S (plus x m) ].
  
let rec plus' n m on m ≝
  match m with
  [ O ⇒ n
  | S x ⇒ S (plus' n x) ].
  
lemma plus_O : ∀y. (y = plus y O).
  assume y : nat
  we proceed by induction on y to prove (y = plus y O)
  case O
    we need to prove (O = plus O O)
    done
  case S (x:nat)
  by induction hypothesis we know (x = plus x O) (IH1)
  we need to prove (S x = plus (S x) O)
  that is equivalent to (S x = S (plus x O))
  by IH1 done
 qed.

lemma replacement : ∀x,z. (plus x (S z)=S (plus x z)).
  assume x:nat
  assume z : nat
  we proceed by induction on x to prove (plus x (S z)=S (plus x z))
  case O
    we need to prove (plus O (S z) = S (plus O z))
    that is equivalent to (S z = S z)
    done
  case S (w:nat)
    by induction hypothesis we know (plus w (S z)=S (plus w z)) (IH1)
    we need to prove (plus (S w) (S z)=S (plus (S w) z))
    that is equivalent to (S (plus w (S z)) = S (S (plus w z)))
    by IH1 done
  qed.

  
theorem plus_plus' : ∀x,y. plus x y = plus' x y.
  assume x : nat
  assume y : nat
  we proceed by induction on y to prove (plus x y = plus' x y)
  case O
    we need to prove (plus x O = plus' x O)
    that is equivalent to (plus x O = x)
    by plus_O done
   case S (z:nat)
    by induction hypothesis we know (plus x z = plus' x z) (IH1)
    we need to prove (plus x (S z) = plus' x (S z))
    that is equivalent to (plus x (S z) = S (plus' x z))
    by IH1, replacement done
  qed.