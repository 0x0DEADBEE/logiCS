(**************************************************************************)
(*       ___                                                              *)
(*      ||M||                                                             *)
(*      ||A||       A project by Andrea Asperti                           *)
(*      ||T||                                                             *)
(*      ||I||       Developers:                                           *)
(*      ||T||         The HELM team.                                      *)
(*      ||A||         http://helm.cs.unibo.it                             *)
(*      \   /                                                             *)
(*       \ /        This file is distributed under the terms of the       *)
(*        v         GNU General Public License Version 2                  *)
(*                                                                        *)
(**************************************************************************)

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

let rec leb n m on n :=
 match n with
 [ O => true
 | S x =>
    match m with
    [ O => false
    | S y => leb x y
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

axiom from_gtb_to_gtP : ∀x,y:nat. (gtb x y = true) → (gtP x y).
axiom ax_plus_inf : ∀x:nat.∃y:nat. gtb y x = true.

theorem test01 : ∀x:nat. ∃y:nat. gtP y x.
  assume x:nat
  by ax_plus_inf we proved (∃z:nat. gtb z x = true) (H1)
  let z:nat such that (gtb z x = true) (H2)
  by H2, from_gtb_to_gtP we proved (gtP z x) (H2b)
  by H2b, ex_intro done
qed.
  




