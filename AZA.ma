include "basics/logic.ma".
include "basics/bool.ma".
include "arithmetics/nat.ma".
include "basics/core_notation.ma".
(*-inf as O*)
(*notes: lt, gt, ge built in*)
(*> = le x y = false
  >= = le x y = false ∨ eq x y = true
  NOTE CAREFULLY: insted of using False, use  ¬
*)
inductive unsigned_nat : Type[0] ≝
  | Num : ℕ → unsigned_nat
  | Inf : unsigned_nat.
  (*single L ⇒ list of nats
    double LL ⇒ list of lists
    single T ⇒ single tuple
    double TT ⇒ list of tuples*)
inductive list : Type[0] ≝
  | Nil : list
  | L : unsigned_nat → list → list.
inductive tuple : Type[0] ≝
  | T : unsigned_nat → unsigned_nat → tuple.
inductive list_tuple : Type[0] ≝
  | Nil : list_tuple
  | TT : tuple → list_tuple → list_tuple.

let rec eq_prop (n:unsigned_nat) (m:unsigned_nat) on n ≝
  match n with
  [ Num (x:ℕ)⇒ 
    match m with
    [ Num (y:ℕ) ⇒ x=y
    | Inf ⇒ False]
  | Inf ⇒
    match m with
    [ Num (y:ℕ) ⇒ False
    | Inf ⇒ True]
  ].

let rec eq_bool (n:unsigned_nat) (m:unsigned_nat) on n ≝
  match n with
  [ Num (x:ℕ)⇒ 
    match m with
    [ Num (y:ℕ) ⇒ eqb x y
    | Inf ⇒ false]
  | Inf ⇒
    match m with
    [ Num (y:ℕ) ⇒ false
    | Inf ⇒ true]
  ].

let rec le_prop (n:unsigned_nat) (m:unsigned_nat) on n ≝
  match n with
  [ Num (x:ℕ)⇒ 
    match m with
    [ Num (y:ℕ) ⇒ x≤y
    | Inf ⇒ True]
  | Inf ⇒
    match m with
    [ Num (y:ℕ) ⇒ False
    | Inf ⇒ True]
  ].
let rec le_bool (n:unsigned_nat) (m:unsigned_nat) on n ≝
  match n with
  [ Num (x:ℕ)⇒ 
    match m with
    [ Num (y:ℕ) ⇒ leb x y
    | Inf ⇒ true]
  | Inf ⇒
    match m with
    [ Num (y:ℕ) ⇒ false
    | Inf ⇒ true]
  ].
axiom le_bool_to_prop : ∀x,y:unsigned_nat. (le_bool x y = true) → le_prop x y.
axiom eq_bool_to_prop : ∀x,y:unsigned_nat. (eq_bool x y = true) → eq_prop x y.
axiom de_morgan_law_and1 : ∀x,y:Prop. ¬(x∧y) → (¬x)∨(¬y).
axiom de_morgan_law_and2 : ∀x,y:Prop. (¬x)∨(¬y) → ¬(x∧y).
axiom de_morgan_law_or1  : ∀x,y:Prop. ¬(x∨y) → (¬x)∧(¬y).
axiom de_morgan_law_or2  : ∀x,y:Prop. (¬x)∧(¬y) → ¬(x∨y).
axiom double_negation1 : ∀x:Prop. (¬¬x) → x.
(*Logica 6: Semantica classica della logica proposizionale slides pg 6/17*)
axiom ax_no_contradiction1 : ∀x:Prop. ((x) → ((¬x) = False)).
axiom ax_no_contradiction2 : ∀x:Prop. (((¬x) = False) → (x)).
axiom ax_annihilation_and1 : ∀x:Prop. (x∧False) = False.
axiom ax_annihilation_and2 : ∀x:Prop. (False∧x) = False.
axiom ax_neutral_element_or: ∀x:Prop. (x∨False) = False.


(*if (x<y) == false then x >= y*)
theorem t00: ∀x,y:unsigned_nat. ¬(le_prop x y∧¬(eq_prop x y)) → (¬(le_prop x y))∨(eq_prop x y).
  assume x:unsigned_nat
  assume y:unsigned_nat
  suppose (¬(le_prop x y∧(¬eq_prop x y))) (H1)
  by H1, de_morgan_law_and1 we proved ((¬(le_prop x y))∨(¬(¬(eq_prop x y)))) (H2)
  we proceed by cases on H2 to prove  (¬le_prop x y∨eq_prop x y)
  case or_introl
    suppose (¬le_prop x y) (H3)
    by H3, or_introl done
  case or_intror
    suppose (¬¬eq_prop x y) (H3)
    by H3, double_negation1 we proved (eq_prop x y) (H4)
    by H4, or_intror done
qed.

(*if x==y then ¬(x<y)∧¬(y<x)*)
theorem t01: ∀x,y:unsigned_nat. eq_prop x y → (¬(le_prop x y ∧ ¬eq_prop x y))∧(¬(le_prop y x ∧ ¬eq_prop x y)).
  assume x:unsigned_nat
  assume y:unsigned_nat
  suppose (eq_prop x y) (H1)
  we need to prove (¬((le_prop x y∧¬eq_prop x y) ∨ (le_prop y x∧¬eq_prop x y))) (KK)
    by H1, ax_no_contradiction1 we proved ((¬eq_prop x y) = False) (H2)
    >H2
    we need to prove  (¬(le_prop x y∧False∨le_prop y x∧False))
    we need to prove ((le_prop x y∧False) = False) (H3)
    by ax_annihilation_and1 done
    >H3
    we need to prove ((le_prop y x∧False) = False) (H4)
    by ax_annihilation_and1 done
    >H4 (*I apply H4*)
    we need to prove  (¬(False∨False))
    we need to prove ((False∨False) = False) (H5)
    by ax_neutral_element_or done
    >H5
    we need to prove  (¬False)
    that is equivalent to (True)
    
  
  
    



  
  
  
  
  
  
