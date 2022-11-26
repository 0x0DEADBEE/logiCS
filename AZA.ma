include "basics/logic.ma".
include "basics/bool.ma".
include "arithmetics/nat.ma".
include "basics/core_notation.ma".
(*-inf as O*)
(*notes: lt, gt, ge built in*)
(*> = le x y = false
  >= = le x y = false ∨ eq x y = true
*)
(*inductive nat : Type[0] ≝
  | O : nat
  | S : nat → nat.*)
inductive unsigned_int : Type[0] ≝
  | Num : ℕ → unsigned_int
  | Inf : unsigned_int.
  (*single L ⇒ list of nats
    double LL ⇒ list of lists
    single T ⇒ single tuple
    double TT ⇒ list of tuples*)
inductive list_nat : Type[0] ≝
  | Nil : list_nat
  | Cons : ℕ → list_nat → list_nat. 
inductive list : Type[0] ≝
  | Nil : list
  | L : unsigned_int → list → list.
inductive tuple : Type[0] ≝
  | T : unsigned_int → unsigned_int → tuple.
inductive list_tuple : Type[0] ≝
  | E : list_tuple (*empty list*)
  | TT : tuple → list_tuple → list_tuple.
  
(*used merely for boolean if-conditions*)
let rec eq (n:unsigned_int) (m:unsigned_int) on n ≝
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

let rec le (n:unsigned_int) (m:unsigned_int) on n ≝
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

let rec plus (x:unsigned_int) (y:unsigned_int) on x ≝
  match x with
  [ Num (z:ℕ) ⇒
    match y with
    [ Num (w:ℕ) ⇒Num (z+w)
    | Inf ⇒ Inf]
  | Inf ⇒ Inf
  ].

definition two : unsigned_int ≝ Num (S(S(O))).
definition one : unsigned_int ≝ Num (S (O)).
definition zero : unsigned_int ≝ Num O.

let rec mult (x:unsigned_int) (y:unsigned_int) on x ≝
  match x with
  [ Num (z:ℕ) ⇒ 
    match y with 
    [ Num (w:ℕ) ⇒ Num (z*w) 
    | Inf ⇒ Inf
    ]
  | Inf ⇒ Inf
  ].


let rec sum_nat (x:ℕ) on x ≝
  match x with
  [ O ⇒ O
  | S (w:ℕ) ⇒ (S w)+ (sum_nat w) 
  ].

theorem gauss : ∀x:ℕ. eqb ((1+1)*(sum_nat x)) (x*(x+1)) = true.
  assume x:ℕ
  we proceed by induction on x to prove  (eqb ((1+1)*sum_nat x) (x*(x+1))=true)
  case O
  done
  case S (w:ℕ)
    by induction hypothesis we know (eqb ((1+1)*sum_nat w) (w*(w+1))=true) (II)
    we need to prove (∀a,b:ℕ. eqb a b=true → a=b)(K1)
    assume a:ℕ
    assume b:ℕ
    suppose (eqb a b=true) (K9)
    done (*eventually It will make it!; let it run for a while*)
    by K1, II we proved ((1+1)*sum_nat w = w*(w+1)) (H1)
    we need to prove (S w = w+1) (K2)
    done
    we need to prove  (eqb ((1+1)*sum_nat (S w)) (S w*(S w+1))=true)
    that is equivalent to  (eqb ((1+1)*((S w)+(sum_nat w))) (S w*(S w+1))=true)
    we need to prove (∀a,b,c:ℕ. a*(b+c) = a*b + a*c) (K3)
    done
    by K3 we proved ((1+1)*(S w+sum_nat w) = (1+1)*(S w) + (1+1)*(sum_nat w)) (K4)
    >K4
    >H1
    we need to prove (S w = w+1) (K5)
    done
    >K5
    we need to prove  ((1+1)*(w+1)+w*(w+1) = (w+1)*(w+1+1)) (K6)
      we need to prove (∀a,b,c:ℕ. a*c + b*c = c*(b+a)) (K7)
      done
      by K7 we proved ((1+1)*(w+1)+w*(w+1) = (w+1)*(w+1+1)) (H2)
      >H2
      done
    >K6
    done
qed.
    

  
let rec get_head (L:list) on L ≝
  match L with
  [ Nil ⇒ Inf
  | L (head:unsigned_int) (tail:list) ⇒ head].
let rec get_tail (L:list) on L ≝ 
  match L with 
  [ Nil ⇒ Nil
  | L (head:unsigned_int) (tail:list) ⇒ tail].
let rec concat (L1:list) (L2:list) on L1 ≝
  match L1 with
  [ Nil ⇒ L2
  | L head tail ⇒ L head (concat tail L2)].
let rec sorted (L1:list) on L1 ≝ 
  match L1 with
  [ Nil ⇒  true
  | L head tail ⇒ (le head (get_head tail))∧sorted tail].


let rec length (L1:list) on L1 ≝ 
  match L1 with
  [ Nil ⇒  zero
  | L head tail ⇒ plus one (length tail)].
  
  
let rec belongs (x:unsigned_int) (L1:list) on L1 ≝
  match L1 with
  [ Nil ⇒ false
  | L head tail ⇒ eq head x ∨(belongs x tail)].

theorem true_equals_false : (true=false) → False.
done
qed.
theorem false_equals_true : (false=true) → False.
done
qed.

notation "'ABSURDUM' A" non associative with precedence 89 for @{'absurdum $A}.
interpretation "ex_false" 'absurdum A = (False_ind ? A).

theorem slide: ∀L1:list. ∃L2:list. (sorted(L2)=true)∧(∀z:unsigned_int. (belongs z L1)=true → (belongs z L2)=true).

(*qualsiasi lista è finita e ha sempre almeno lunghezza zero*)
theorem test: ∀l:list. (((le (length l) (Inf)) = true)∧(((le (length l) zero)=false)∨((eq (length l) zero)=true))).
  assume l:list
  we proceed by induction on l to prove ( (le (length l) Inf=true∧(le (length l) zero=false∨eq (length l) zero=true)))
  case Nil
    we need to prove  (le (length Nil) Inf=true∧(le (length Nil) zero=false∨eq (length Nil) zero=true))
    that is equivalent to  (le zero Inf=true∧(le zero zero=false∨eq (length Nil) zero=true))
    done
  case L (head:unsigned_int) (tail:list)
    by induction hypothesis we know (le (length tail) Inf=true∧(le (length tail) zero=false∨eq (length tail) zero=true)) (II)
    we need to prove (le (length (L head tail)) Inf=true∧(le (length (L head tail)) zero=false∨eq (length (L head tail)) zero=true))
    that is equivalent to (le (plus one (length tail)) Inf=true∧(le (length (L head tail)) zero=false∨eq (length (L head tail)) zero=true))
    that is equivalent to (le (plus one (length tail)) Inf=true∧(le (plus one (length tail)) zero=false∨eq (length (L head tail)) zero=true))
    that is equivalent to (le (plus one (length tail)) Inf=true∧(le (plus one (length tail)) zero=false∨eq (plus one (length tail)) zero=true))
    we need to prove (∀x:unsigned_int. le x Inf=true) (H1)
      assume x:unsigned_int
      we proceed by induction on x to prove  (le x Inf=true)
      case Num (w:ℕ)
      done
      case Inf
      done
    by H1 we proved (le (plus one (length tail)) Inf=true) (H2)
    we need to prove (∀x:unsigned_int. le (plus one x) zero = false) (H3)
      assume x:unsigned_int
      we proceed by induction on x to prove  (le (plus one x) zero=false)
      case Num (w:ℕ)
      done
      case Inf
      done
    by H3 we proved ((le (plus one (length tail)) zero)=false) (H4)
    by H4, or_introl we proved (le (plus one (length tail)) zero=false∨eq (plus one (length tail)) zero=true) (H5)
    by H2, H5, conj done
qed.
    
      
          
  


(* with equal sign then Prop! IMPORTANTE
let rec test00 n on n ≝
  match n with
  [Num (x:ℕ) ⇒ if (le (Num O) (Num O)) then (le (Num O) (Num O))=false else False
  |Inf ⇒ False].
theorem test02: ∀b:bool. (b = false ) ∧(b=true) → (b=false).

theorem test01 : ∀x,y:ℕ. (lt x y) ∨ (le x y).
IMPORTANTE
*)



 (*ex esame 16/02/2022*)
(* per farlo funzionare, settare il caso base di get_head a Num O o zero
let rec comb (L1:list) (L2:list) on L1 ≝
  match L1 with
  [Nil ⇒ E
  |L (head:unsigned_int) (tail:list) ⇒ (TT (T head (get_head L2)) (comb tail (get_tail L2)))].
let rec test (t:tuple) on t ≝
  match t with
  [T x y ⇒ eq x y].
let rec red (L:list_tuple) on L ≝
  match L with
  [ E ⇒ true
  | TT (head:tuple) (tail:list_tuple) ⇒ (test head)∧(red tail)].

theorem ex160222 : ∀x:list. red(comb x x)=true.
  assume x:list
  we proceed by induction on x to prove  (red (comb x x)=true)
  case Nil
    we need to prove  (red (comb Nil Nil)=true)
    that is equivalent to  (red E=true)
    that is equivalent to (true = true)
    done
  case L (head:unsigned_int) (tail:list)
    by induction hypothesis we know (red (comb tail tail)=true) (II)
    we need to prove  (red (comb (L head tail) (L head tail))=true)
    that is equivalent to  (red ((TT (T head (get_head (L head tail))) (comb tail (get_tail (L head tail)))))=true)
    that is equivalent to  (red (TT (T head head) (comb tail (get_tail (L head tail)))) =true)
    that is equivalent to  (red (TT (T head head) (comb tail tail))=true)
    (*qui per problemi sintattici mi ero bloccato.. tutto assieme*)
    that is equivalent to  ((test (T head head)∧red (comb tail tail)) = true)
    that is equivalent to  ((eq head head∧red (comb tail tail))=true)
    we need to prove (eq head head = true) (KK)
      we proceed by induction on head to prove  (eq head head=true)
      case Num (x:ℕ)
        we need to prove  (eq (Num x) (Num x)=true)
        that is equivalent to (eqb x x=true)
        done
      case Inf
        we need to prove  (eq Inf Inf=true)
        done
    >KK
    by II done
qed.
*)
(*
Considerate la seguente sintassi per le liste di numeri interi:

L ::= [] | Z::L

dove il non-terminale Z genera tutti i numeri interi e :: è associativo a destra.

Considerate il seguente codice che definisce le funzioni @ (concatenazione di due liste), sorted (che ritorna true sse la lista in input è ordinata), hd (che ritorna la testa di una lista non vuota o più infinito se la lista è vuota) e bubble_up (utilizzata come funzione ausiliaria per definire l'algoritmo di ordinamento noto con il nome di bubble sort).

[] @ L = L

(x::tl) @ L = x :: (tl @ L)

sorted([]) = tt

sorted(x::tl) = x <= hd(tl) && sorted(tl)

hd([]) = +oo

hd(x::tl) = x

bubble_up(x,[]) = x::[]

bubble_up(x,y::tl) = if x <= y then x::bubble_up(y,tl) else y::bubble_up(x,tl)



Dimostrate, per induzione su L, che per ogni x, se sorted(x::L) = tt allora bubble_up(x,L) = x::L.
*)

let rec bubble_up (x:unsigned_int) (l:list) on l ≝
  match l with
  [ Nil ⇒ L x Nil
  | L y tl ⇒ if (le x y) then (L x (bubble_up y tl)) else (L y (bubble_up x tl))].

theorem da_virtuale0 : ∀y:list. ∀x:unsigned_int. (sorted (L x y)=true) → (bubble_up x y) = (L x y).
  assume y:list
  we proceed by induction on y to prove  (∀x:unsigned_int.sorted (L x y)=true→bubble_up x y=L x y)
  case Nil
    we need to prove  (∀x:unsigned_int.sorted (L x Nil)=true→bubble_up x Nil=L x Nil)
    that is equivalent to  (∀x:unsigned_int. (((le x (get_head Nil))∧(sorted Nil))=true→bubble_up x Nil=L x Nil))
    that is equivalent to  (∀x:unsigned_int.(le x Inf∧sorted Nil)=true→bubble_up x Nil=L x Nil)
    that is equivalent to  (∀x:unsigned_int.(le x Inf∧true)=true→bubble_up x Nil=L x Nil)
    that is equivalent to  (∀x:unsigned_int.(le x Inf∧true)=true→L x Nil=L x Nil)
    we need to prove (∀x:unsigned_int. le x Inf = true) (KK)
      assume x:unsigned_int
      we proceed by induction on x to prove  (le x Inf=true)
      case Num (z:nat)
      we need to prove  (le (Num z) Inf=true)
      done
      case Inf
      done
    by KK done
  case L (head:unsigned_int) (tail:list)
    by induction hypothesis we know (∀x:unsigned_int.sorted (L x tail)=true→bubble_up x tail=L x tail) (II)
    we need to prove  (∀x:unsigned_int. sorted (L x (L head tail))=true→bubble_up x (L head tail)=L x (L head tail))
    that is equivalent to  (∀x:unsigned_int. ((le x (get_head (L head tail)))∧sorted (L head tail))=true→bubble_up x (L head tail)=L x (L head tail))
    that is equivalent to (∀x:unsigned_int. ((le x head)∧sorted (L head tail))=true→bubble_up x (L head tail)=L x (L head tail))
    that is equivalent to (∀x:unsigned_int. ((le x head)∧((le head (get_head (tail)))∧sorted(tail)))=true→bubble_up x (L head tail)=L x (L head tail))
    that is equivalent to (∀x:unsigned_int. ((le x head)∧((le head (get_head (tail)))∧sorted(tail)))=true→
if (le x head) then (L x (bubble_up head tail)) else (L head (bubble_up x tail)) 
=L x (L head tail))
    assume x:unsigned_int
    we proceed by cases on (le x head) to prove  ((le x head∧(le head (get_head tail)∧sorted tail))=true
  →if le x head then L x (bubble_up head tail) else L head (bubble_up x tail) 
   =L x (L head tail))
      case true
        we need to prove  ((true∧(le head (get_head tail)∧sorted tail))=true
  →if true then L x (bubble_up head tail) else L head (bubble_up x tail) 
   =L x (L head tail))
        that is equivalent to  ((true∧(le head (get_head tail)∧sorted tail))=true→L x (bubble_up head tail) =L x (L head tail))
        that is equivalent to (((le head (get_head tail)∧sorted tail))=true→L x (bubble_up head tail) =L x (L head tail))
        suppose (((le head (get_head tail)∧sorted tail))=true) (H1)
        we need to prove (∀a,b:bool. (a∧b)=true → (a=true)∧(b=true)) (KK)
          assume a:bool
          assume b:bool
          we proceed by induction on a to prove  ((a∧b)=true→a=true∧b=true)
          case true
            done
          case false
            done
            
        by H1 we have ((le head (get_head tail)) = true) (H1a) and ((sorted tail) = true) (H1b)
        (*ora dobbiamo tramite le ipotesi H1{a.b} sfrittare le ipotesi induttiva con un risultato intermedio*)
        we need to prove ((sorted tail=true)∧(le head (get_head tail)=true) → sorted (L head tail)=true) (HH)
          we proceed by induction on tail to prove  (sorted tail=true∧le head (get_head tail)=true→sorted (L head tail)=true)
          case Nil
            we need to prove  (sorted Nil=true∧le head (get_head Nil)=true→sorted (L head Nil)=true)
            that is equivalent to  (true=true∧le head Inf=true→sorted (L head Nil)=true)
            we need to prove (le head Inf = true) (LL)
              we proceed by induction on head to prove  (le head Inf=true)
              case Num (n:nat)
              done
              case Inf
              done
            done
          case L (hd:unsigned_int) (tl:list)
            by induction hypothesis we know ((sorted tl=true∧le head (get_head tl)=true→sorted (L head tl)=true)) (IH)
            we need to prove  (sorted (L hd tl)=true∧le head (get_head (L hd tl))=true→sorted (L head (L hd tl))=true)
            that is equivalent to (sorted (L hd tl)=true∧le head hd=true→sorted (L head (L hd tl))=true)
            that is equivalent to   (((le hd (get_head tl))∧sorted tl)=true∧le head hd=true→sorted (L head (L hd tl))=true)
            that is equivalent to (((le hd (get_head tl))∧sorted tl)=true∧le head hd=true→((le head (get_head (L hd tl)))∧sorted (L hd tl))=true)
            that is equivalent to (((le hd (get_head tl))∧sorted tl)=true∧le head hd=true→((le head hd)∧sorted (L hd tl))=true)
            that is equivalent to (((le hd (get_head tl))∧sorted tl)=true∧le head hd=true→((le head hd)∧((le hd (get_head tl))∧sorted tl))=true)
            suppose ((le hd (get_head tl)∧sorted tl)=true∧le head hd=true) (H2)
            by H2 we have ((le hd (get_head tl)∧sorted tl)=true) (H2a) and (le head hd=true) (H2b)
            by H2a, H2b done
        by HH, H1a, H1b we proved (sorted (L head tail)=true) (H2)
        by H2, II we proved (bubble_up head tail=L head tail) (H3)
        >H3
        done
      case false
        suppose ((false∧(le head (get_head tail)∧sorted tail))=true) (H1)
        we need to prove (∀b:bool. (false∧b)=true → False) (H2)
          done
        by H1 we proved (False) (ABS)
        using (ABSURDUM ABS)
        done
qed.

theorem plus_commutative : ∀x,y:unsigned_int. plus x y = plus y x.
  assume x:unsigned_int
  assume y:unsigned_int
  we proceed by induction on x to prove  (plus x y=plus y x)
  case Num (w:nat)
    we proceed by induction on y to prove  (plus (Num w) y=plus y (Num w))
    case Num (z:ℕ)
    we need to prove  (plus (Num w) (Num z)=plus (Num z) (Num w))
    that is equivalent to (Num (w+z) = Num (z+w))
    done
    case Inf
    done
  case Inf
    we proceed by induction on y to prove (plus Inf y=plus y Inf)
    case Num (z:ℕ)
    done
    case Inf
    done
qed.
  
(*(∀x.∃y.x ≤ k + y + (−k)) ⇒ ∀y.∃x.k + y ≤ k + x*)
theorem ex9_20220526 : (∀k:unsigned_int. (∀x:unsigned_int. ∃y:unsigned_int. (le (plus x k) (plus k y))=true)→ (∀a:unsigned_int. ∃b:unsigned_int. (le (plus k a) (plus k b))=true)).
  assume k:unsigned_int
  suppose (∀x:unsigned_int.∃y:unsigned_int.le (plus x k) (plus k y)=true) (H1)
  assume a:unsigned_int
  by H1 we proved (∃y:unsigned_int.le (plus a k) (plus k y)=true) (H2)
  let y:unsigned_int such that (le (plus a k) (plus k y)=true) (H3)
  by plus_commutative we proved (plus k a = plus a k) (H4)
  by H3,ex_intro done
qed.

theorem test2 : ∀l:list. eq (length l) Inf = false.
  assume l:list
  we proceed by induction on l to prove  (eq (length l) Inf=false)
  case Nil
  done
  case L (head:unsigned_int) (tail:list)
  by induction hypothesis we know (eq (length tail) Inf=false) (II)
  we need to prove  (eq (length (L head tail)) Inf=false)
  that is equivalent to  (eq (plus one (length tail)) Inf=false)
  we need to prove (eq (length tail) Inf=false →  eq (plus one (length tail)) Inf=false) (H1)
    (*non + affatto banale, length di tail può essere ancora infinito*)
    we proceed by induction on (length tail) to prove  (eq (length tail) Inf=false→eq (plus one (length tail)) Inf=false)
    case Num (w:nat)
    done
    case Inf
    done
  by H1 we proved  (eq (plus one (length tail)) Inf=false) (H2)
  done
qed.



    
    
   

  
  
  
  
  
  
