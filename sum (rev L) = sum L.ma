include "basics/logic.ma".
inductive nat : Type[0] ≝
   O : nat
 | S : nat → nat.
 inductive list_nat : Type[0] ≝
   Nil : list_nat
 | Cons : nat → list_nat → list_nat.
 let rec plus n m on n ≝
 match n with
 [ O ⇒ m
 | S x ⇒ S (plus x m) ].
 let rec sum L on L ≝
 match L with
 [ Nil ⇒ O
 | Cons N TL ⇒ plus N (sum TL)
 ].
 (*definite la funzione che inserisce un numero in
      coda a una lista*)
 let rec enqueue n L on L ≝
 match L with
 [ Nil ⇒ Cons n Nil
 | Cons head tail ⇒ Cons head (enqueue n tail)
 ].

(*e usatela per definire la funzione rev che restituisce
      la lista ottenuta leggendo la lista in input dalla fine all'inizio*)
let rec rev L on L ≝
  match L with
  [ Nil ⇒ Nil
  | Cons head tail ⇒ enqueue head (rev tail)
  ].
  
lemma l6: ∀H. (plus H (S O)=S (plus H O)).
  assume H:nat
  we proceed by induction on H to prove (plus H (S O)=S (plus H O))
  case O
    we need to prove  (plus O (S O)=S (plus O O))
    done
  case S (x:nat)
    by induction hypothesis we know (plus x (S O)=S (plus x O)) (II)
    we need to prove (plus (S x) (S O)=S (plus (S x) O))
    that is equivalent to (plus (S x) (S O)=S (S(plus x O)))
    that is equivalent to (S (plus x (S O))=S (S((plus x O))))
    done
qed.

lemma l8: ∀H.  (plus H (S (S O))=S (S (plus H O))).
  assume H:nat
  we proceed by induction on H to prove  (plus H (S (S O))=S (S (plus H O)))
  case O
    we need to prove  (plus O (S (S O))=S (S (plus O O)))
    done
   case S (x:nat)
    by induction hypothesis we know (plus x (S (S O))=S (S (plus x O))) (II)
    we need to prove  (plus (S x) (S (S O))=S (S (plus (S x) O)))
    that is equivalent to  (plus (S x) (S (S O))=S (S (S(plus x O))))
    that is equivalent to (S(plus x (S (S O)))=S (S (S (plus x O))))
    done
  qed.
  
(*semplifichiamo lemma l7*)
lemma l9 : ∀H,w. (plus H (S (S w))=S (S (plus H w))).
  assume H:nat
  assume w:nat
  we proceed by induction on H to prove (plus H (S (S w))=S (S (plus H w)))
  case O
    we need to prove  (plus O (S (S w))=S (S (plus O w)))
    done
  case S(x:nat)
    by induction hypothesis we know (plus x (S (S w))=S (S (plus x w))) (II)
    we need to prove  (plus (S x) (S (S w))=S (S (plus (S x) w)))
    that is equivalent to  (plus (S x) (S (S w))=S (S (S(plus x w))))
    that is equivalent to (S(plus x (S (S w)))=S (S (S (plus x w))))
    by II done
 qed.

lemma l7: ∀H,x. (plus H (S (S (plus x O)))=S (S (plus H (plus x O)))).
  assume H:nat
  assume x:nat
  we proceed by induction on x to prove (plus H (S (S (plus x O)))=S (S (plus H (plus x O))))
  case O
    we need to prove  (plus H (S (S (plus O O)))=S (S (plus H (plus O O))))
    that is equivalent to  (plus H (S (S O))=S (S (plus H O)))
    done
   case S (w:nat)
    by induction hypothesis we know (plus H (S (S (plus w O)))=S (S (plus H (plus w O)))) (II)
    we need to prove (plus H (S (S (plus (S w) O)))=S (S (plus H (plus (S w) O))))
    that is equivalent to (plus H (S (S (S(plus w O))))=S (S (plus H (S(plus w O)))))
    by II done
 qed.

lemma l5:  ∀H,w. (plus H (S (plus w O))=S (plus H (plus w O))).
  assume H:nat
  assume w:nat
  we proceed by induction on w to prove (plus H (S (plus w O))=S (plus H (plus w O)))
  case O
    we need to prove  (plus H (S (plus O O))=S (plus H (plus O O)))
    that is equivalent to  (plus H (S O)=S (plus H O))
    by l6 done
  case S(x:nat)
    by induction hypothesis we know (plus H (S (plus x O))=S (plus H (plus x O))) (II)
    we need to prove  (plus H (S (plus (S x) O))=S (plus H (plus (S x) O)))
    that is equivalent to  (plus H (S (plus (S x) O))=S (plus H (S(plus x O))))
    that is equivalent to  (plus H (S (plus (S x) O))=S (plus H (S(plus x O))))
    that is equivalent to  (plus H (S (S(plus x O)))=S (plus H (S (plus x O))))
    done
 qed.

lemma l4: ∀H,N. (plus H (plus N O)=plus N (plus H O)).
  assume H:nat
  assume N:nat
  we proceed by induction on N to prove (plus H (plus N O)=plus N (plus H O))
  case O
    we need to prove  (plus H (plus O O)=plus O (plus H O))
    that is equivalent to  (plus H O=plus H O)
    done
  case S (w:nat)
    by induction hypothesis we know (plus H (plus w O)=plus w (plus H O)) (II)
    we need to prove  (plus H (plus (S w) O)=plus (S w) (plus H O))
    that is equivalent to  (plus H (S (plus w O))= S (plus w (plus H O)))
    by l5, II done
 qed.
 
lemma l11: ∀H,w,X. (plus H (S (plus w X))=S (plus H (plus w X))).
  assume H:nat
  assume w:nat
  assume X:nat
  we proceed by induction on w to prove (plus H (S (plus w X))=S (plus H (plus w X)))
  case O
    we need to prove  (plus H (S (plus O X))=S (plus H (plus O X)))
    that is equivalent to  (plus H (S X)=S (plus H X))
    we proceed by induction on H to prove (plus H (S X)=S (plus H X))
      case O
        we need to prove  (plus O (S X)=S (plus O X))
        done
      case S (y:nat)
        by induction hypothesis we know (plus y (S X)=S (plus y X)) (II)
        we need to prove  (plus (S y) (S X)=S (plus (S y) X))
        that is equivalent to  (S(plus y (S X))=S( S(plus y X)))
        done
   case S (y:nat)
     by induction hypothesis we know ((plus H (S (plus y X))=S (plus H (plus y X)))) (II)
     we need to prove (plus H (S (plus (S y) X))=S (plus H (plus (S y) X)))
     that is equivalent to  (plus H (S (S(plus y X)))=S (plus H (S(plus y X))))
     done
  qed.
 
(*lemma l3 semplificato*)
lemma l10 : ∀H,N,X. (plus H (plus N X)=plus N (plus H X)).
  assume H:nat
  assume N:nat
  assume X:nat
  we proceed by induction on N to prove (plus H (plus N X)=plus N (plus H X))
  case O
    we need to prove  (plus H (plus O X)=plus O (plus H X))
    that is equivalent to  (plus H X=plus H X)
    done
  case S (w:nat)
    by induction hypothesis we know (plus H (plus w X)=plus w (plus H X)) (II)
    we need to prove  (plus H (plus (S w) X)=plus (S w) (plus H X))
    that is equivalent to  (plus H (S(plus w X))=S(plus w (plus H X)))
    done
  qed.

lemma l3: ∀H,N,T. (plus H (plus N (sum T))=plus N (plus H (sum T))).
  assume H:nat
  assume N:nat
  assume T:list_nat
  we proceed by induction on T to prove (plus H (plus N (sum T))=plus N (plus H (sum T)))
    case Nil
      we need to prove  (plus H (plus N (sum Nil))=plus N (plus H (sum Nil)))
      that is equivalent to (plus H (plus N O)=plus N (plus H O))
      done
    case Cons (head:nat) (tail:list_nat)
      by induction hypothesis we know (plus H (plus N (sum tail))=plus N (plus H (sum tail))) (II)
      we need to prove  (plus H (plus N (sum (Cons head tail)))=plus N (plus H (sum (Cons head tail))))
      that is equivalent to  (plus H (plus N (sum (Cons head tail)))=plus N (plus H (plus head (sum tail))))
      that is equivalent to  (plus H (plus N (plus head (sum tail)))=plus N (plus H (plus head (sum tail))))
      by II, l10 done
qed.


(*problema piu' ordinato rispetto a l1 ma identico*)
lemma l2 : ∀L,N. (sum (enqueue N L)=plus N (sum L)).
  assume L:list_nat
  assume N:nat
  we proceed by induction on L to prove (sum (enqueue N L)=plus N (sum L))
  case Nil
    we need to prove (sum (enqueue N Nil)=plus N (sum Nil))
    that is equivalent to (sum (Cons N Nil)=plus N O)
    done
   case Cons (H:nat) (T:list_nat)
      by induction hypothesis we know (sum (enqueue N T)=plus N (sum T)) (II)
      we need to prove  (sum (enqueue N (Cons H T))=plus N (sum (Cons H T)))
      that is equivalent to  (sum (Cons H (enqueue N T))=plus N (sum (Cons H T)))
      that is equivalent to  (plus H (sum (enqueue N T))=plus N (sum (Cons H T)))
      that is equivalent to  (plus H (sum (enqueue N T))=plus N (plus H (sum T)))
      by II, l3 done
   qed.
      
  
lemma l1 : ∀tail,head. (sum (enqueue head (rev tail))=plus head (sum (rev tail))).
  assume tail:list_nat
  assume head : nat
  we proceed by induction on tail to prove (sum (enqueue head (rev tail))=plus head (sum (rev tail)))
  case Nil
     we need to prove (sum (enqueue head (rev Nil))=plus head (sum (rev Nil)))
     that is equivalent to  (sum (enqueue head Nil)=plus head (sum Nil))
     that is equivalent to (sum (Cons head Nil)=plus head O)
     that is equivalent to (plus head (sum Nil)=plus head O)
     done
   case Cons (HEAD:nat) (TAIL:list_nat)
      by induction hypothesis we know (sum (enqueue head (rev TAIL))=plus head (sum (rev TAIL))) (II)
      we need to prove  (sum (enqueue head (rev (Cons HEAD TAIL)))=plus head (sum (rev (Cons HEAD TAIL))))
      that is equivalent to (sum (enqueue head (enqueue HEAD (rev TAIL)))=plus head (sum (rev (Cons HEAD TAIL))))
      that is equivalent to (sum (enqueue head (enqueue HEAD (rev TAIL)))=plus head (sum (enqueue HEAD (rev TAIL))))
      by II, l2 done
   qed.
      
      
      
  
theorem ex10 : ∀L. sum (rev L) = sum L.
  assume L: list_nat
  we proceed by induction on L to prove (sum (rev L) = sum L)
  case Nil
    we need to prove (sum (rev Nil) = sum Nil)
    that is equivalent to (sum Nil = sum Nil)
    done
  case Cons (head:nat) (tail:list_nat)
    by induction hypothesis we know (sum (rev tail) = sum tail) (II)
    we need to prove  (sum (rev (Cons head tail))=sum (Cons head tail))
    that is equivalent to (sum (enqueue head (rev tail))=plus head (sum tail))
    by l1, II done
 qed.
 
    