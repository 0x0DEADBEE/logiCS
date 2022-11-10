include "basics/logic.ma".
(*
include "basics/lists/list.ma".
include "arithmetics/nat.ma".
include "basics/core_notation.ma".
*)
(* Ignorate la seguente linea *)
axiom daemon : False.

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

lemma plus_same : ∀head. (plus head O = plus head O).
assume head :nat
  we proceed by induction on head to prove (plus head O = plus head O)
  case O
    we need to prove (plus O O = plus O O)
    done
  case S (w:nat)
  by induction hypothesis we know (plus w O = plus w O) (IH1)
  we need to prove (plus (S w) O = plus (S w) O)
  done

qed.

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
    

theorem if_both_zero : ∀l1,l2,head. ((sumL l1 = sumL l2) ∧ (sumL l1 = O)) → (plus head (sumL l2) = plus head O).
  assume l1: list_nat
  assume l2: list_nat
  assume head: nat
  suppose ((sumL l1 = sumL l2) ∧ (sumL l1 = O)) (H1)
  by H1 we have (sumL l1 = sumL l2) (H2) and (sumL l1 = O) (H3)
  by H2, H3 we proved (sumL l2 = O) (H4)
  we need to prove (plus head (sumL l2)=plus head O)
  by H4, plus_O, plus_same done
 qed.

lemma sumL_trans : ∀l1,l2,l3. (((sumL l1 = sumL l2) ∧ (sumL l2 = sumL l3)) → (sumL l1 = sumL l3)).
  assume l1 : list_nat
  assume l2 : list_nat
  assume l3 : list_nat
  (*senza assunzioni avrebbe gaveuppato*)
  suppose (((sumL l1 = sumL l2) ∧ (sumL l2 = sumL l3))) (H1)
  by H1 we have (sumL l1 = sumL l2) (H2) and (sumL l2 = sumL l3) (H3)
  done
 qed.
 
 
lemma inner_or_outer_S : ∀e. (S (plus e (plus O O))=plus e (S (plus O O))).
  assume e:nat
  we proceed by induction on e to prove  (S (plus e (plus O O))=plus e (S (plus O O)))
  case O
    we need to prove  (S (plus O (plus O O))=plus O (S (plus O O)))
    done
   case S (w:nat)
    by induction hypothesis we know (S (plus w (plus O O))=plus w (S (plus O O))) (IH1)
    we need to prove  (S (plus (S w) (plus O O))=plus (S w) (S (plus O O)))
    that is equivalent to  (S (plus (S w) O )=plus (S w) (S O))
    that is equivalent to (S (S (plus w O))=S (plus w (S O)))
    by IH1 done
  qed.
    
    
 
 lemma s_spitted_out : ∀w,e. (S (plus e (plus w O))=plus e (S (plus w O))).
 assume w:nat
 assume e:nat
 we proceed by induction on w to prove (S (plus e (plus w O))=plus e (S (plus w O)))
 case O
  we need to prove  (S (plus e (plus O O))=plus e (S (plus O O)))
  that is equivalent to (S (plus e O)=plus e (S O))
  by inner_or_outer_S done
 case S (x:nat)
  by induction hypothesis we know (S (plus e (plus x O))=plus e (S (plus x O))) (IH1)
  we need to prove  (S (plus e (plus (S x) O))=plus e (S (plus (S x) O)))
  that is equivalent to  (S (plus e (S (plus x O)))=plus e (S (S (plus x O))))
  by IH1, inner_or_outer_S, plus_O, plus_same done

 lemma comm : ∀ hd,e. (plus hd (plus e O) = plus e (plus hd O)).
  assume hd: nat
  assume e:nat
  we proceed by induction on hd to prove (plus hd (plus e O) = plus e (plus hd O))
  case O
    we need to prove (plus O (plus e O) = plus e (plus O O))
    that is equivalent to (plus e O = plus e O)
    done
  case S (w:nat)
    by induction hypothesis we know (plus w (plus e O) = plus e (plus w O)) (IH1)
    we need to prove  (plus (S w) (plus e O)=plus e (plus (S w) O))
    that is equivalent to (S (plus w (plus e O))= plus e (S (plus w O))) 
    
lemma s_spitted_out : ∀w,e. (S (plus e (plus w O))=plus e (S (plus w O))).

lemma same_sum : ∀hd,tail,e.  (plus hd (sumL (insertAtBottomL tail e))=plus e (sumL (Cons hd tail))).
  assume hd:nat
  assume tail : list_nat
  assume e: nat
  we proceed by induction on tail to prove (plus hd (sumL (insertAtBottomL tail e))=plus e (sumL (Cons hd tail)))
  case Nil
    we need to prove (plus hd (sumL (insertAtBottomL Nil e))=plus e (sumL (Cons hd Nil)))
    that is equivalent to (plus hd (sumL (Cons e Nil) )= plus e (plus hd (sumL Nil)))
    that is equivalent to (plus hd (plus e (sumL Nil)) = plus e (plus hd O))
    that is equivalent to (plus hd (plus e O) = plus e (plus hd O))
    done
  
  
theorem if_eq_then : ∀l1,l2,e. (sumL l1 = sumL l2) → (sumL (insertAtBottomL l1 e) = plus e (sumL l2)).
  assume l1: list_nat
  assume l2: list_nat
  assume e : nat
  suppose (sumL l1 = sumL l2) (H1)
  we need to prove (sumL (insertAtBottomL l1 e) = plus e (sumL l2))
  we proceed by induction on l1 to prove (sumL (insertAtBottomL l1 e) = plus e (sumL l2))
  case Nil
    we need to prove (sumL (insertAtBottomL Nil e) = plus e (sumL l2))
    that is equivalent to (sumL (Cons e Nil) = plus e (sumL l2))
    that is equivalent to (plus e (sumL Nil) = plus e (sumL l2))
    that is equivalent to (plus e O = plus e (sumL l2))
    cases daemon
    (*by H1, if_both_zero done*)
  case Cons (hd: nat) (tail: list_nat)
    by induction hypothesis we know (sumL (insertAtBottomL tail e) = plus e (sumL l2)) (IH1)
    (*la nuova II non dovrebbe essere falsa?*)
    we need to prove (sumL (insertAtBottomL (Cons hd tail) e) = plus e (sumL l2))
    that is equivalent to (sumL (Cons hd (insertAtBottomL tail e)) = plus e (sumL l2))
    that is equivalent to (plus hd (sumL (insertAtBottomL tail e)) = plus e (sumL l2))
    
  
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
    
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  

