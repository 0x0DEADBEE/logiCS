include "basics/logic.ma".
include "arithmetics/nat.ma".
include "basics/bool.ma".
include "basics/core_notation.ma".
lemma true_or_false: ∀b. b = true ∨ b = false.
  //
qed.

inductive list_nat : Type[0] ≝
  | Nil : list_nat
  | Cons : ℕ → list_nat → list_nat.

let rec insert n L on L ≝
  match L with
  [ Nil ⇒ Cons n Nil
  | Cons head tail ⇒
    if (leb n head) then (Cons n (Cons head tail))
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
    if (leb Y H) then (Cons Y (Cons H T))
    else (Cons H (insert Y T))
  ) → X=Y∨((H=X)∨(belong X T)))
  by true_or_false we proved ((leb Y H = true) ∨ (leb Y H = false)) (TF)
  we proceed by cases on TF to prove  (belong X (if (leb Y H) then Cons Y (Cons H T) else Cons H (insert Y T) )
  →X=Y∨(H=X∨belong X T))
  case or_introl
    suppose (leb Y H=true) (H1)
    we need to prove (belong X (Cons Y (Cons H T) ) →X=Y∨(H=X∨belong X T)) (KK)
      that is equivalent to ((Y=X)∨(belong X (Cons H T))→X=Y∨(H=X∨belong X T))
      that is equivalent to  (Y=X∨((H=X)∨(belong X T))→X=Y∨(H=X∨belong X T))
      suppose (Y=X∨(H=X∨belong X T)) (H2)
      we proceed by cases on H2 to prove  (X=Y∨(H=X∨belong X T))
      case or_introl
        suppose (Y=X) (H3)
        done
      case or_intror
        suppose (H=X∨belong X T) (H3)
        done
     (* Quello che fa è usare l'ipotesi H1 del tipo "E1 = E2"
rimpiazzando nella conclusione (quello che devi dimostrare) tutte le
occorrenze di E1 con E2.*)
     >H1 (*(if leb Y H then ⇒ if true then*)
     by KK done
  case or_intror
    suppose (leb Y H=false) (H1)
    >H1
    we need to prove  (belong X (Cons H (insert Y T)) →X=Y∨(H=X∨belong X T)) (KK)
      that is equivalent to ((H=X)∨( belong X  (insert Y T))→X=Y∨(H=X∨belong X T))
      suppose (H=X∨belong X (insert Y T)) (H2)
      we proceed by cases on H2 to prove  (X=Y∨(H=X∨belong X T))
      case or_introl
        suppose (H=X) (H3)
        done
        
      case or_intror
        suppose (belong X (insert Y T)) (H3)
        by H3, or_intror we proved ((H=X)∨(belong X (insert Y T))) (H4)
        by H3, II we proved (X=Y∨belong X T) (H5)
        we proceed by cases on H5 to prove  (X=Y∨(H=X∨belong X T))
        case or_introl
          suppose (X=Y) (H6)
          done
        case or_intror
          suppose (belong X T) (H6)
          done
     by H1, KK done
 
 qed.
  
  
theorem bb : ∀X,Y,L. ( ((X=Y)∨(belong X L)) → (belong X (insert Y L))).
  assume X:ℕ 
  assume Y:ℕ 
  assume L:list_nat
  suppose ((X=Y)∨(belong X L)) (H1)
  we proceed by cases on H1 to prove  (belong X (insert Y L))
  case or_introl
    suppose (X=Y) (H2)
    we proceed by induction on L to prove  (belong X (insert Y L))
    case Nil
      we need to prove  (belong X (insert Y Nil))
      that is equivalent to  (belong X (Cons Y Nil))
      that is equivalent to ((Y=X)∨(belong X Nil))
      that is equivalent to ((Y=X)∨False)
      by H2,or_introl done
    case Cons (head:ℕ) (tail:list_nat)
      by induction hypothesis we know (belong X (insert Y tail)) (II)
      we need to prove (belong X (insert Y (Cons head tail)))
      that is equivalent to (belong X (
      if (leb Y head) then (Cons Y (Cons head tail))
      else (Cons head (insert Y tail))))
      by true_or_false we proved ((leb Y head = true) ∨ (leb Y head = false)) (TF)
      we proceed by cases on TF to prove  (belong X
  (if leb Y head then Cons Y (Cons head tail) else Cons head (insert Y tail) ))
      case or_introl
        suppose (leb Y head=true) (T)
        we need to prove (belong X (Cons Y (Cons head tail))) (KK)
          that is equivalent to ((Y=X)∨(belong X (Cons head tail)))
          that is equivalent to ((Y=X)∨((head=X)∨(belong X tail)))
          by H2,or_introl done
        >T
        by T, KK done
      
      case or_intror
        suppose (leb Y head=false) (F)
        we need to prove (belong X (Cons head (insert Y tail))) (KK)
          that is equivalent to ((head=X)∨(belong X (insert Y tail)))
          by II,or_intror done
        >F
        by F, KK done
   
   case or_intror
    (*
    suppose (belong X L) (H2)
    we proceed by induction on L to prove  (belong X (insert Y L))
      case Nil
      we need to prove  (belong X (insert Y Nil))
      that is equivalent to  (belong X (Cons Y Nil))
      that is equivalent to ((Y=X)∨(belong X Nil))
      that is equivalent to ((Y=X)∨False)*)
      we proceed by induction on L to prove  (belong X L→belong X (insert Y L))
      case Nil
        we need to prove  (belong X Nil→belong X (insert Y Nil))
        that is equivalent to (False→belong X (Cons Y Nil))
        done
      case Cons (head:ℕ) (tail:list_nat)
        by induction hypothesis we know (belong X tail→belong X (insert Y tail)) (II)
        we need to prove  (belong X (Cons head tail)→belong X (insert Y (Cons head tail)))
        that is equivalent to  ((head=X)∨(belong X tail)→belong X (insert Y (Cons head tail)))
        that is equivalent to  (head=X∨belong X tail→belong X ( if (leb Y head) then (Cons Y (Cons head tail)) else (Cons head (insert Y tail))))
        by true_or_false we proved (leb Y head=true ∨ leb Y head=false) (TF)
        we proceed by cases on TF to prove (head=X∨belong X tail→belong X (if leb Y head then Cons Y (Cons head tail) else Cons head (insert Y tail) ))
        case or_introl
          suppose (leb Y head=true) (T)
          suppose (head=X∨belong X tail) (H2)
          we need to prove (belong X (Cons Y (Cons head tail))) (KK)
            that is equivalent to ((Y=X)∨(belong X (Cons head tail)))
            that is equivalent to ((Y=X)∨((head=X)∨(belong X tail)))
            by H2, or_intror done
          >T
          by T, KK done
        case or_intror
          suppose (leb Y head=false) (F)
          suppose (head=X∨belong X tail) (H2)
          we need to prove ((belong X (Cons head (insert Y tail)))) (KK)
            that is equivalent to  ((head=X)∨(belong X (insert Y tail)))
            we proceed by cases on H2 to prove  (head=X∨belong X (insert Y tail))
            case or_introl
              suppose (head=X) (H3)
              by H3, or_introl done
            case or_intror
              suppose (belong X tail) (H3)
              by H3, II we proved (belong X (insert Y tail)) (H4)
              by H4, or_intror done
          >F
          by F, KK done
          
          
     qed.
  
  
  
  
  
  
  
  
  
  
  