include "basics/logic.ma".
include "arithmetics/nat.ma".
include "basics/bool.ma".
include "basics/core_notation.ma".
inductive list_nat : Type[0] ≝
  | Nil : list_nat
  | Cons : ℕ → list_nat → list_nat.
inductive tuple_nat : Type[0] ≝
  | Nil : tuple_nat
  | Cons : ℕ → ℕ → tuple_nat.
inductive list_tuple : Type[0] ≝
  | Nil : list_tuple
  | Cons : tuple_nat → list_tuple → list_tuple.

let rec eqb n m on n ≝
  match n with
  [ O ⇒
    match m with
    [ O ⇒ true
    | S y ⇒ false]
  | S x ⇒ 
    match m with
    [ O ⇒ false
    | S y ⇒ eqb x y
    ]
  ].

let rec eqP n m on n ≝
  match n with
  [ O ⇒
    match m with
    [ O ⇒ True
    | S y ⇒ False]
  | S x ⇒ 
    match m with
    [ O ⇒ False
    | S y ⇒ eqP x y
    ]
  ].

let rec ltb n m on n ≝
  match n with
  [ O ⇒
    match m with
    [ O ⇒ false
    | S y ⇒ true
    ]
  | S x ⇒
    match m with
    [ O ⇒ false
    | S y ⇒ ltb x y
    ]
  ].
  
let rec ltP n m on n ≝
  match n with
  [ O ⇒
    match m with
    [ O ⇒ False
    | S y ⇒ True
    ]
  | S x ⇒
    match m with
    [ O ⇒ False
    | S y ⇒ ltP x y
    ]
  ].

let rec leb n m on n :=
 match n with
 [ O ⇒ true
 | S x ⇒ 
    match m with
    [ O ⇒ false
    | S y ⇒ leb x y
    ]
 ].

let rec leP n m on n :=
 match n with
 [ O => True
 | S x =>
    match m with
    [ O => False
    | S y => leP x y
    ]
 ].

let rec gtb n m on n :=
match n with
 [ O => false
 | S x =>
  match m with
  [ O => true
  | S y => gtb x y
  ]
 ].
 
let rec gtP n m on n :=
 match n with
 [ O => False
 | S x =>
    match m with
    [ O => True
    | S y => gtP x y
    ]
 ].

(*to use only after you supposed (true=false) ! *)
axiom true_eq_false_then_F : (true=false)∨(false=true) → False.
axiom if_else : ∀b:bool. b=true∨b=false.
axiom def_list_nat : ∀L:list_nat. L=Nil∨(∃H:ℕ. ∃T:list_nat. L=(Cons H T)).
axiom def_nat : ∀x:ℕ. x=O∨(∃y:ℕ. x= S y).
axiom eq_bool_to_P : ∀x,y:ℕ. (eqb x y = true) → (eqP x y).
axiom le_bool_to_P : ∀x,y:ℕ. (leb x y = true) → (leP x y).
axiom lt_bool_to_P : ∀x,y:ℕ. (ltb x y = true) → (ltP x y).
axiom gt_bool_to_P : ∀x,y:ℕ. (gtb x y = true) → (gtP x y).
axiom ax_plus_inf : ∀x:ℕ.∃y:ℕ. gtb y x = true.
axiom ax_minus_inf : ∀x:ℕ.∃y:ℕ. ltb y x = true.

 

theorem test00 : ∀x:ℕ. ∃y:ℕ. gtP y x.
  assume x:ℕ
  by ax_plus_inf we proved (∃z:ℕ. gtb z x = true) (H1)
  let z:ℕ such that (gtb z x = true) (H2)
  by H2, gt_bool_to_P we proved (gtP z x) (H2b)
  by H2b, ex_intro done
qed.

theorem test01: ∀x:ℕ. ∃y:ℕ. (ltb y x = true).
  assume x:ℕ
  by ax_minus_inf we proved (∃z:ℕ. ltb z x = true) (H1)
  let z:ℕ such that (ltb z x = true) (H2)
  by H2, ex_intro done
qed.

theorem test02: ∀x,y:ℕ. ltP x y → gtP y x.
  assume x:ℕ
  we proceed by induction on x to prove  (∀y:ℕ. ltP x y→gtP y x)
  case O
    we need to prove  (∀y:ℕ. ltP O y→gtP y O)
    assume y:ℕ 
    by def_nat we proved (y=O∨(∃x:ℕ. y= S x)) (H1)
    we proceed by cases on H1 to prove  (ltP O y→gtP y O)
    case or_introl
      suppose (y=O) (H2)
      >H2
      we need to prove  (ltP O O→gtP O O)
      that is equivalent to (False → False)
      suppose (False) (ABS)
      done
    case or_intror
      suppose (∃w:ℕ.y=S w) (H2)
      let w:ℕ such that (y=S w) (H2b)
      >H2b
      we need to prove  (ltP O (S w)→gtP (S w) O)
      that is equivalent to (True→ True)
      done
  case S (w:ℕ)
    by induction hypothesis we know (∀y:ℕ. ltP w y→gtP y w) (II)
    assume y:ℕ
    by def_nat we proved (y=O∨(∃x:ℕ. y= S x)) (H1)
    we proceed by cases on H1 to prove  (ltP (S w) y→gtP y (S w))
    case or_introl
      suppose (y=O) (H2)
      >H2
      we need to prove  (ltP (S w) O→gtP O (S w))
      that is equivalent to (False → False)
      done
    case or_intror
      suppose (∃z:ℕ.y=S z) (H2)
      let z:ℕ such that (y=S z) (H3)
      >H3
      we need to prove  (ltP (S w) (S z)→gtP (S z) (S w))
      that is equivalent to (ltP w z →gtP z w)
      by II done
qed.

let rec get_head_list_nat (L:list_nat) on L ≝ 
  match L with
  [ Nil ⇒ O
  | Cons H T ⇒ H
  ].
let rec get_tail_list_nat (L:list_nat) on L ≝ 
  match L with
  [ Nil ⇒ Nil
  | Cons H T ⇒ T
  ].

let rec length L on L ≝
  match L with
  [ Nil ⇒ O
  | Cons H T ⇒ S (length T)].
  
let rec concat L1 L2 on L1 ≝
  match L1 with
  [ Nil ⇒ L2
  | Cons H T ⇒ Cons H (concat T L2)].
let rec sorted L on L ≝
  match L with
  [ Nil ⇒ True
  | Cons H T ⇒ leP H (get_head_list_nat T) ∧ sorted (T)].
  
(*TODO: ge and +INF/-INF notations*)
  







