include "arithmetics/nat.ma".
include "basics/lists/list.ma".

(* Ignorate la seguente linea *)
axiom daemon : False.

lemma true_or_false: ∀b: bool. b = true ∨ b = false.
 //
qed.

(* listN ::= nil | cons ℕ listN *)

(* 29/06/2022, esercizio 7 *)
let rec isHead x l on l ≝
 match l with
 [ nil ⇒ false
 | cons y l' ⇒ eqb x y ].

(*

  uniq [1,1,3,4,4,5] = [1,3,4,5]
  
  uniq [1,3,4,4,5] = [1,3,4,5]

*)

let rec uniq l on l ≝
 match l with
 [ nil ⇒ nil ?
 | cons x l ⇒
    if (isHead x (uniq l))
    then (uniq l)
    else (cons ? x (uniq l))
 ].

theorem isHead_uniq1:
 ∀l,x,y. isHead x l = true → isHead y l = true → x = y.
assume l : (list ℕ)
we proceed by induction on l to prove
 (∀x,y. isHead x l = true → isHead y l = true → x = y)
case nil
  we need to prove
   (∀x,y. isHead x [] = true → isHead y [] = true → x = y)
  that is equivalent to
   (∀x,y. false = true → false = true → x = y)
  assume x : ℕ
  assume y : ℕ
  suppose (false = true) (abs) (* ipotesi assurda *)
  cases daemon (* INTERROMPO LA PROVA IN QUANTO OVVIA
                  DAL FALSO DIMOSTRO QUALUNQUE COSA *)

case cons (h : ℕ) (tl : (list ℕ))
  suppose
   (∀x,y. isHead x tl = true → isHead y tl = true → x = y)
   (II)
  we need to prove
   (∀x,y. isHead x (cons ? h tl) = true → isHead y (cons ? h tl) = true → x = y)
  that is equivalent to
   (∀x,y. eqb x h = true → eqb y h = true → x = y)
  assume x : ℕ
  assume y : ℕ
  suppose (eqb x h = true) (H1)
  suppose (eqb y h = true) (H2)
  (* eqb_true_to_eq dice che se la FUNZIONE (codice!)
     eqb restituisce true, allora i suoi input sono uguali *)
  by eqb_true_to_eq, H1 we proved (x = h) (H11)
  by eqb_true_to_eq, H2 we proved (y = h) (H21)
  by H11, H21
done
qed.

theorem isHead_uniq:
 ∀l,x. isHead x l = isHead x (uniq l).
assume l : (list ℕ)
we proceed by induction on l to prove
 (∀x. isHead x l = isHead x (uniq l))
case nil
  we need to prove
   (∀x. isHead x (nil ?) = isHead x (uniq (nil ?)))
  that is equivalent to
   (∀x. false = isHead x (nil ?))
  that is equivalent to
   (∀x. false = false)
done
case cons (h : ℕ) (tl : (list ℕ))
 suppose  (∀x. isHead x tl = isHead x (uniq tl)) (II)
 we need to prove
   (∀x. isHead x (cons ? h tl) = isHead x (uniq (cons ? h tl)))
 that is equivalent to
  (∀x. eqb x h =
    isHead x
     (if (isHead h (uniq tl))
     then (uniq tl)
     else (cons ? h (uniq tl))))
 assume x : ℕ
 by true_or_false we proved
  (isHead h (uniq tl) = true ∨
   isHead h (uniq tl) = false) (TF)
 we proceed by cases on TF to prove
  (eqb x h =
     isHead x
      (if (isHead h (uniq tl))
      then (uniq tl)
      else (cons ? h (uniq tl))))
 case or_introl
  suppose (isHead h (uniq tl) = true) (T)
  we need to prove (eqb x h = isHead x (uniq tl)) (L)
  (*
     se eqb x h = true allora
       x = h  per eqb_true_to_eq (AAA)
     e devo dimostrare true = isHead x (uniq tl)
     per AAA 
     mi riduco a dimostrare true = isHead h (uniq tl)
     ovvio per T
     
     se eqb x h = false allora
      not (x = h) per eqb_false_to_not_eq (BBB)
     e devo dimostrare false = isHead x (uniq tl)
     da T e isHead_uniq1 ho x ≠ h
     e ...
  *)
    cases daemon (* INTERROMPO LA DIMOSTRAZIONE:
                    ovvio per T e isHead_uniq1 *)
  ] cases daemon

 case or_intror
  suppose (isHead h (uniq tl) = false) (F)
  we need to prove
   (eqb x h = isHead x (cons ? h (uniq tl))) (L)
  that is equivalent to (eqb x h = eqb x h)
  done
done
qed.

(* commutatività della somma *)

(* ℕ ::= O | S ℕ *)
inductive N : Type[0] ≝
   O : N
 | S : N → N.
 
(* plus O m = m
   plus (S n) m = S (plus n m) *)
let rec plus n m on n ≝
 match n with
 [ O ⇒ m
 | S x ⇒ S (plus x m) ].

(* 4 = S (S (S (S O))) = S 3 = S (S 2) = ...

  plus 100 2
→ S (plus 99 2)
→ S (S (plus 98 2))
→ ...
→ S (S (S ... (plus O 2)))
→ S (S (S ... (S 2))) = 102

  plus 2 100
→ S (plus 1 100)
→ S (S (plus 0 100))
→ S (S 100) = 102

*)

lemma plus_O : ∀m. m = plus m O.
assume m : N
we proceed by induction on m to prove (m = plus m O)
case O
 we need to prove (O = plus O O)
 that is equivalent to (O = O)
 done
case S (x: N)
 suppose (x = plus x O) (II)
 we need to prove (S x = plus (S x) O)
 that is equivalent to (S x = S (plus x O))
 by II
done
qed.

lemma plus_S: ∀m,x. S (plus m x) = plus m (S x).
assume m : N
we proceed by induction on m to prove
 (∀x. S (plus m x) = plus m (S x))
case O
 we need to prove
  (∀x. S (plus O x) = plus O (S x))
 that is equivalent to
  (∀x. S x = S x)
done
case S (y: N)
 suppose (∀x. (S (plus y x) = plus y (S x))) (II)
 we need to prove
  (∀x. S (plus (S y) x) = plus (S y) (S x))
 that is equivalent to
  (∀x. S (S (plus y x)) = S (plus y (S x)))
 assume x : N
 by II
done
qed.

theorem comm_plus: ∀n,m. plus n m = plus m n.
assume n : N
we proceed by induction on n to prove
 (∀m. plus n m = plus m n)
case O
 we need to prove
  (∀m. plus O m = plus m O)
 that is equivalent to
  (∀m. m = plus m O)
 by plus_O
done
case S (x: N)
 suppose (∀m. plus x m = plus m x) (II)
 we need to prove (∀m. plus (S x) m = plus m (S x))
 that is equivalent to (∀m. S (plus x m) = plus m (S x))
 assume m : N
 by II, plus_S
done
qed.



 
