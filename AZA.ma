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

definition one : unsigned_int ≝ Num (S (O)).
definition zero : unsigned_int ≝ Num O.
let rec length (L1:list) on L1 ≝ 
  match L1 with
  [ Nil ⇒  zero
  | L head tail ⇒ plus one (length tail)].
  
theorem true_equals_false : (true=false) → False.
done
qed.
theorem false_equals_true : (false=true) → False.
done
qed.

(*
(*qualsiasi lista è finita e ha sempre almeno lunghezza zero*)
theorem test: ∀l:list. (((le (length l) (Inf)) = true)∧(((le (length l) zero)=false)∨((eq (length l) zero)=true))).
  assume l:list
  we proceed by induction on l to prove  (le (length l) Inf=true∧(le (length l) (Num O)=false∨eq (length l) (Num O)=true))
  case Nil
    we need to prove  (le (length Nil) Inf=true∧(le (length Nil) (Num O)=false∨eq (length Nil) (Num O)=true))
    that is equivalent to  (le (Num O) Inf=true∧(le (Num O) (Num O)=false∨eq (Num O) (Num O)=true))
    done
  case L (h:unsigned_int) (t:list)
    by induction hypothesis we know (le (length t) Inf=true∧(le (length t) (Num O)=false∨eq (length t) (Num O)=true)) (II)
    we need to prove  (le (length (L h t)) Inf=true∧(le (length (L h t)) (Num O)=false∨eq (length (L h t)) (Num O)=true))
    that is equivalent to (le (length (L h t)) Inf=true∧(le (length (L h t)) (Num O)=false∨eq (plus (Num (S (O))) (length t)) (Num O)=true))
    that is equivalent to (le (plus (Num (S (O))) (length t)) Inf=true∧(le (plus (Num (S (O))) (length t)) (Num O)=false∨eq (plus (Num (S (O))) (length t)) (Num O)=true))
    by II we have (le (length t) Inf=true) (IIa) and (le (length t) (Num O)=false∨eq (length t) (Num O)=true) (IIb)
    we need to prove (∀x:unsigned_int. le x Inf = true) (H1)
      assume x:unsigned_int
      we proceed by induction on x to prove  (le x Inf=true)
      case Num (y:ℕ)
        done
      case Inf
        done
    we proceed by cases on IIb to prove  (le (plus (Num 1) (length t)) Inf=true∧(le (plus (Num 1) (length t)) (Num O)=false∨eq (plus (Num 1) (length t)) (Num O)=true))
    case or_introl
      suppose (le (length t) (Num O)=false) (H2)
      we need to prove (∀x:unsigned_int. (eq x (Num O) = false) → le x (Num O) = false) (H3)
        assume x:unsigned_int
        we proceed by induction on x to prove  (eq x (Num O)=false→le x (Num O)=false)
        case Num (y:ℕ)
          we need to prove  (eq (Num y) (Num O)=false→le (Num y) (Num O)=false)
          we proceed by induction on y to prove  (eq (Num y) (Num O)=false→le (Num y) (Num O)=false)
          case O
          we need to prove  (eq (Num O) (Num O)=false→le (Num O) (Num O)=false)
          that is equivalent to  (true=false→le (Num O) (Num O)=false)
          suppose (true=false) (NEQ)
          by true_equals_false, NEQ we proved (False) (ABS)
          done
          case S (w:ℕ)
          done
        case Inf
          done
      we need to prove eq (plus (Num 1) (length t)) 
      by H3 we proved (le (plus (Num 1) (length t)) (Num O)=false) (H4)*)
          
  
notation "'ABSURDUM' A" non associative with precedence 89 for @{'absurdum $A}.
interpretation "ex_false" 'absurdum A = (False_ind ? A).

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
(* per farlo funzionare, settare il caso base di get_head a Num O
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
            

    
    
   

  
  
  
  
  
  
