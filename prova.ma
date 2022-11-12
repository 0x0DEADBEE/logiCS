include "basics/logic.ma".
include "arithmetics/nat.ma".
include "basics/bool.ma".
include "basics/core_notation.ma".
lemma true_or_false: ∀b. b = true ∨ b = false.
  //
qed.

let rec leqb n m on n :=
 match n with
 [ O => True
 | S x =>
    match m with
    [ O => False
    | S y => leqb x y
    ]
 ].

notation "'ABSURDUM' A" non associative with precedence 89 for @{'absurdum $A}.
interpretation "ex_false" 'absurdum A = (False_ind ? A).
axiom assurdo_1 : (true=false) → False.
axiom assurdo_2 : (false=true) → False.
axiom le_from_bool_to_prop : ∀x,H. (leb x H=true) → (leqb x H = True).

 
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
     
(*dimostrate che se X appartiene alla lista L allora appartiene alla
         lista sort L*)
theorem c : ∀X,L. belong X L → belong X (sort L).
  assume X:nat
  assume L:list_nat
  we proceed by induction on L to prove  (belong X L→belong X (sort L))
  case Nil
    we need to prove  (belong X Nil→belong X (sort Nil))
    that is equivalent to  (False→belong X Nil)
    done
  case Cons (H:ℕ) (T:list_nat)
    by induction hypothesis we know (belong X T → belong X (sort T)) (II)
    we need to prove  (belong X (Cons H T)→belong X (sort (Cons H T)))
    that is equivalent to  ((H=X)∨(belong X T)→belong X (sort (Cons H T)))
    that is equivalent to  (H=X∨belong X T→belong X (insert H (sort T)))
    suppose (H=X∨belong X T) (H1)
    
    we proceed by cases on H1 to prove  (belong X (insert H (sort T)))
    case or_introl
      suppose (H=X) (H2)
      (*per bb, per dimostrarlo, mi riduco a dimostrare l'antecedente*)
      we need to prove ((X=H)∨(belong X (sort T))) (H3)
        by H2,or_introl done
      by H3,bb done
    case or_intror
      suppose (belong X T) (H2)
      by H2, II we proved (belong X (sort T)) (H3)
      by bb, or_intror, H3 done
   qed.
      


(*QUANDO ABBIAMO IN MENTE DI PROCEDERE PER INDUZIONE STRUTTURALE, NON SUPPORRE!*)
(* d) dimostrate anche il viceversa*)
theorem d : ∀X,L. belong X (sort L) → belong X L.
  assume X:ℕ
  assume L:list_nat
  (*
  suppose (belong X (sort L)) (H1)
  we proceed by induction on L to prove  (belong X L)
    case Nil
      we need to prove  (belong X Nil)
      that is equivalent to (False)*)
  we proceed by induction on L to prove  (belong X (sort L)→belong X L)
    case Nil
      we need to prove  (belong X (sort Nil)→belong X Nil)
      that is equivalent to (False → False)
      done
    case Cons (H:ℕ) (T:list_nat)
      by induction hypothesis we know (belong X (sort T) → belong X T) (II)
      we need to prove  (belong X (sort (Cons H T))→belong X (Cons H T))
      that is equivalent to  (belong X (sort (Cons H T))→(H=X)∨(belong X T))
      that is equivalent to  (belong X (insert H (sort T))→H=X∨belong X T)
      suppose (belong X (insert H (sort T))) (H1)
      we need to prove ((X=H)∨(belong X (sort T))) (H2)
        by b, H1 done
      we proceed by cases on H2 to prove  (H=X∨belong X T)
      case or_introl
        suppose (X=H) (H3)
        done
      case or_intror
        suppose (belong X (sort T)) (H3)
        by H3, II we proved (belong X T) (H4)
        by H4, or_intror done
  qed.
  
  
let rec isEmpty L on L ≝
  match L with
  [ Nil ⇒ true
  | Cons head tail ⇒ false
  ].

let rec getHead L on L ≝
  match L with
  [ Nil ⇒ O
  | Cons head tail ⇒ head
  ].
(*La funzione è per ricorsione sul primo argomento (è il "on n" nella
prima riga) e infatti l'unica chiamata ricorsiva "leqb x y" avviene sul
primo parametro attuale x che è ottenuto dal pattern "S x" quando si
analizza n. Il "match" annidato semplicemente analizza la forma di "m",
ma non giustifica per se alcuna chiamata ricorsiva: è una definizione
per casi, non per ricorsione.*)

(*e) definite, per ricorsione strutturale, il predicato ``X è ordinata''*)
let rec ordered L on L ≝
  match L with
  [ Nil ⇒ True
  | Cons head tail ⇒ if (isEmpty tail) then True else ((leqb head (getHead tail))∧ordered tail)
  ].
  
(*dimostrate che se L è ordinata lo è anche la lista ottenuta inserendo
         X in L*) 

theorem f : ∀L,x. ordered L → ordered (insert x L).
  assume L:list_nat
  assume x:ℕ
  
  we proceed by induction on L to prove (ordered L → ordered (insert x L))
  case Nil
    we need to prove  (ordered Nil→ordered (insert x Nil))
    that is equivalent to  (True→ordered (insert x Nil))
    that is equivalent to  (True→ordered (Cons x Nil))
    that is equivalent to  (True→(if (isEmpty Nil) then True else ((leqb x (getHead Nil))∧ordered Nil)))
    that is equivalent to  (True→if true then True else (leqb x O∧True) )
    done
  case Cons (H:ℕ) (T:list_nat)
    by induction hypothesis we know (ordered T → ordered (insert x T)) (II)
    we need to prove  (ordered (Cons H T)→ordered (insert x (Cons H T)))
    that is equivalent to (if (isEmpty T) then True else (leqb H (getHead T)∧ordered T) →ordered (insert x (Cons H T)))
    that is equivalent to (if isEmpty T then True else (leqb H (getHead T)∧ordered T)
    → ordered (if (leb x H) then (Cons x (Cons H T)) else (Cons H (insert x T))))
    by true_or_false we proved (isEmpty T=true ∨isEmpty T = false) (H3)
    we proceed by cases on H3 to prove   (if isEmpty T then True else (leqb H (getHead T)∧ordered T) 
  →ordered (if leb x H then Cons x (Cons H T) else Cons H (insert x T) ))
    case or_introl
      suppose (isEmpty T=true) (H2)
      we need to prove  (True →ordered (if leb x H then Cons x (Cons H T) else Cons H (insert x T) )) (KK)
      suppose (True) (TRUE)
      by true_or_false we proved (leb x H = true ∨ leb x H = false) (H4)
      we proceed by cases on H4 to prove  (ordered (if leb x H then Cons x (Cons H T) else Cons H (insert x T) ))
      case or_introl
        suppose (leb x H=true) (H5)
         we need to prove  (ordered (Cons x (Cons H T))) (KK)
         that is equivalent to (if (isEmpty (Cons H T)) then True else ((leqb x (getHead (Cons H T)))∧ordered (Cons H T)))
         that is equivalent to  (if false then True else (leqb x H)∧ordered (Cons H T))
         that is equivalent to  (leqb x H ∧ordered (Cons H T))
         that is equivalent to  (leqb x H∧(if (isEmpty T) then True else ((leqb H (getHead T)∧ordered T))))
         >H2
         we need to prove (leqb x H∧if true then True else (leqb H (getHead T)∧ordered T) )
         that is equivalent to (leqb x H ∧ True)
         by le_from_bool_to_prop, H5 we proved (leqb x H = True) (H6)
        by H6, conj, TRUE done
      >H5
      we need to prove 
       (ordered (if true then Cons x (Cons H T) else Cons H (insert x T) ))
      that is equivalent to  (ordered (Cons x (Cons H T)))
      by KK done
     case or_intror
      suppose (leb x H=false) (H5)
      >H5
      we need to prove  (ordered (if false then Cons x (Cons H T) else Cons H (insert x T) ))
      that is equivalent to (ordered (Cons H (insert x T) ))
      that is equivalent to  (if (isEmpty ((insert x T))) then True else ((leqb H (getHead (insert x T)))∧ordered (insert x T)))
      by true_or_false we proved (isEmpty (insert x T) = true ∨ isEmpty (insert x T) = false) (H1)
      we proceed by cases on H1 to prove  (if isEmpty (insert x T) then True else (leqb H (getHead (insert x T))∧ordered (insert x T)) )
      case or_introl
        suppose (isEmpty (insert x T)=true) (H6)
        >H6
        we need to prove  (if true then True else (leqb H (getHead (insert x T))∧ordered (insert x T)) )
        that is equivalent to  (True)
        done
      case or_intror
        suppose (isEmpty (insert x T)=false) (H6)
        >H6
        we need to prove  (if false then True else (leqb H (getHead (insert x T))∧ordered (insert x T)) )
        that is equivalent to  (leqb H (getHead (insert x T))∧ordered (insert x T))
        we need to prove (∀l. (isEmpty l = true) → (ordered l)) (H7)
          assume l:list_nat
          we proceed by induction on l to prove   (isEmpty l=true→ordered l)
          case Nil
            we need to prove  (isEmpty Nil=true→ordered Nil)
            that is equivalent to  (true=true→True)
            done
          case Cons (H:ℕ) (TL:list_nat)
            by induction hypothesis we know ((isEmpty TL = true) → (ordered TL)) (KK)
            we need to prove  (isEmpty (Cons H TL)=true→ordered (Cons H TL))
            that is equivalent to  (false=true→ordered (Cons H TL))
            suppose (false=true) (ABS)
            by ABS, assurdo_2 we proved False (DONE)
            using (ABSURDUM DONE)
            done
        by H7, H2,conj  we proved (ordered T) (H8)
        by H5,II we proved  (ordered (insert x T)) (H9)
        we need to prove (∀A,B. isEmpty A = true → (getHead (insert B A) = B)) (K1)
          assume A:list_nat
          assume B:ℕ
          we proceed by induction on A to prove  (isEmpty A=true→getHead (insert B A)=B)
          case Nil
            we need to prove  (isEmpty Nil=true→getHead (insert B Nil)=B)
            that is equivalent to  (true=true→getHead (Cons B Nil)=B)
            that is equivalent to  (true=true→B=B)
            done
          case Cons (HD:ℕ) (TL:list_nat)
            by induction hypothesis we know ((isEmpty TL=true→getHead (insert B TL)=B)) (KK)
            we need to prove  (isEmpty (Cons HD TL)=true→getHead (insert B (Cons HD TL))=B)
            that is equivalent to  (false=true→getHead (insert B (Cons HD TL))=B)
            suppose (false=true) (ABS)
            by ABS, assurdo_2 we proved False (DONE)
            using (ABSURDUM DONE)
            done
        by K1, H2 we proved (getHead (insert x T)=x) (K2)
        >K2
        we need to prove  ((leb x H=false) → (leb H x=true)) (K3)
          we proceed by induction on x to prove  (leb x H=false→leb H x=true)
          case O
            we need to prove  (leb O H=false→leb H O=true)
            that is equivalent to  (true=false→leb H O=true)
            suppose (true=false) (K3)
            by K3, assurdo_1 we proved False (K4)
            using (ABSURDUM K4)
            done
          case S (w:ℕ)
            by induction hypothesis we know (leb w H=false→leb H w=true) (KK)
            we need to prove  (leb (S w) H=false→leb H (S w)=true)
            that is equivalent to  (leb (S w) H=false→leb H (S w)=true)
            
            
         

(*my ex
Considerare la seguente sintassi per liste di numeri naturali  L ::= [] | ℕ : L , la sintassi C ::= <ℕ, ℕ> per coppie di naturali e le seguenti funzioni definite per ricorsione strutturale:

comb [] l = l
comb (x:l1) l2 = <x, hd l2> : comb l1 (tl l2)
hd [] = 0
hd (x:l) = x
tl [] = []
tl (x:l) = l
red [] = tt
red (c:l) = test c && red l
test < x, y > = x ==y

dove tt è il booleano true, && la congiunzione di booleani, e == la funzione che confronta due numeri tornano tt sse sono uguali.

Dimostrare, per induzione strutturale, il seguente enunciato:
∀l. red (comb l l) = tt*)
inductive tupla : Type[0] ≝
  | Nil : tupla
  | Cons : ℕ → ℕ → tupla.
  
inductive list_tuple : Type[0] ≝
  | Nil : list_tuple
  | Cons: tupla → list_tuple → list_tuple.

let rec getTail L on L ≝
  match L with
  [ Nil ⇒ Nil
  | Cons head tail ⇒ tail].

let rec comb l1 (l2:list_tuple) on l1 ≝
  match l1 with
  [ Nil ⇒ l2 
  | Cons head tail ⇒ Cons (Cons head (getHead l2)) comb l1 (getTail l2)].

  
  
  
  
  
  
  
  
  