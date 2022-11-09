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

lemma plus_O : ∀y. (y = plus' O y).
  assume y : nat
  we proceed by induction on y to prove (y = plus' O y)
  case O
    we need to prove (O = plus' O O)
    that is equivalent to (O = O)
    done
   case S (x :nat)
    by induction hypothesis we know (x = plus' O x) (IH1)
    we need to prove (S x = plus' O (S x))
    that is equivalent to (S x = S (plus' O x))
    by IH1
   done
  qed.

lemma replacement : ∀z,y. (S (plus' z y)=plus' (S z) y).
  assume z : nat
  assume y : nat
  we proceed by induction on y to prove (S (plus' z y)=plus' (S z) y)
  case O
    we need to prove (S (plus' z O)=plus' (S z) O)
    that is equivalent to (S z = S z)
    done
  case S (x : nat)
    by induction hypothesis we know (S (plus' z x)=plus' (S z) x) (IH1)
    we need to prove (S (plus' z (S x))=plus' (S z) (S x))
    that is equivalent to (S (S (plus' z x))=S (plus' (S z) x))
    by IH1 done
qed.

theorem plus_plus' : ∀x,y. plus x y = plus' x y.
  assume x : nat
  assume y : nat
  we proceed by induction on x to prove (plus x y = plus' x y)
  case O
    we need to prove (plus O y = plus' O y)
    that is equivalent to (y = plus' O y)
    by plus_O
   done
   
  case S (z : nat)
    by induction hypothesis we know (plus z y = plus' z y) (IH1)
    we need to prove (plus (S z) y = plus' (S z) y)
    that is equivalent to (S (plus z y) = plus' (S z) y)
    by replacement, IH1 done
qed.