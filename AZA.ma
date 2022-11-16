include "basics/logic.ma".
include "basics/bool.ma".
inductive star : Type[0] ≝ 
  | One : star
  | S : star → star.
inductive int : Type[0] ≝
  | Minus_inf : int
  | Minus : star → int
  | Zero : int
  | Plus : star → int
  | Plus_inf : int.
let rec le_star_prop (n:star) (m:star) on n ≝
  match n with
  [ One ⇒ True
  | S (x:star) ⇒
    match m with
    [ One ⇒ False
    | S (y:star) ⇒ le_star_prop x y]  
  ].

let rec le_prop (n:int) (m:int) on n ≝
  match n with
  [ Minus_inf ⇒ True
  | Minus (x:star) ⇒
    match m with
    [ Minus_inf ⇒ False
    | Minus (y:star) ⇒ le_star_prop y x
    | Zero ⇒ True
    | Plus (z:star) ⇒ True
    | Plus_inf ⇒ True
    ]
  | Zero ⇒
    match m with
    [ Minus_inf ⇒ False
    | Minus (y:star) ⇒ False
    | Zero ⇒ True
    | Plus (z:star) ⇒ True
    | Plus_inf ⇒ True
    ]
  | Plus (y:star) ⇒
    match m with
    [ Minus_inf ⇒ False
    | Minus (z:star) ⇒ False
    | Zero ⇒ False
    | Plus (w:star) ⇒ le_star_prop y w
    | Plus_inf ⇒ True
    ]
  | Plus_inf ⇒
    match m with
    [ Minus_inf ⇒ False
    | Minus (x:star) ⇒ False
    | Zero ⇒ False
    | Plus (y:star) ⇒ False
    | Plus_inf ⇒ True
    ]
  ].
  
let rec le_star_bool (n:star) (m:star) on n ≝
  match n with
  [ One ⇒ true
  | S (x:star) ⇒
    match m with
    [ One ⇒ false
    | S (y:star) ⇒ le_star_bool x y]  
  ].


let rec le_bool (n:int) (m:int) on n ≝
  match n with
  [ Minus_inf ⇒ true
  | Minus (x:star) ⇒
    match m with
    [ Minus_inf ⇒ false
    | Minus (y:star) ⇒ le_star_bool y x
    | Zero ⇒ true
    | Plus (z:star) ⇒ true
    | Plus_inf ⇒ true
    ]
  | Zero ⇒
    match m with
    [ Minus_inf ⇒ false
    | Minus (y:star) ⇒ false
    | Zero ⇒ true
    | Plus (z:star) ⇒ true
    | Plus_inf ⇒ true
    ]
  | Plus (y:star) ⇒
    match m with
    [ Minus_inf ⇒ false
    | Minus (z:star) ⇒ false
    | Zero ⇒ false
    | Plus (w:star) ⇒ le_star_bool y w
    | Plus_inf ⇒ true
    ]
  | Plus_inf ⇒
    match m with
    [ Minus_inf ⇒ false
    | Minus (x:star) ⇒ false
    | Zero ⇒ false
    | Plus (y:star) ⇒ false
    | Plus_inf ⇒ true
    ]
  ].

axiom le_bool_prop: ∀x,y:int. le_bool x y=true → le_prop x y.
let rec ge_star_prop (n:star) (m:star) on n ≝
  match n with
  [ One ⇒ 
    match m with
    [ One ⇒ True
    | S (y:star) ⇒ False]
  | S (x:star) ⇒
    match m with
    [ One ⇒ True
    | S (y:star) ⇒ ge_star_prop x y]  
  ].
let rec ge_prop (n:int) (m:int) on n ≝
  match n with
  [ Minus_inf ⇒ 
    match m with
    [ Minus_inf  ⇒ True
    | Minus (x:star) ⇒ False
    | Zero ⇒ False
    | Plus (y:star) ⇒ False
    | Plus_inf ⇒ False
    ]
  | Minus (x:star) ⇒
    match m with
    [ Minus_inf ⇒ True
    | Minus (y:star) ⇒ ge_star_prop y x
    | Zero ⇒ False
    | Plus (z:star) ⇒ False
    | Plus_inf ⇒ False
    ]
  | Zero ⇒
    match m with
    [ Minus_inf ⇒ True
    | Minus (y:star) ⇒ True
    | Zero ⇒ True
    | Plus (z:star) ⇒ False
    | Plus_inf ⇒ False
    ]
  | Plus (y:star) ⇒
    match m with
    [ Minus_inf ⇒ True
    | Minus (z:star) ⇒ True
    | Zero ⇒ True
    | Plus (w:star) ⇒ ge_star_prop y w
    | Plus_inf ⇒ False
    ]
  | Plus_inf ⇒ True
  ].
  
let rec ge_star_bool (n:star) (m:star) on n ≝
  match n with
  [ One ⇒ 
    match m with
    [ One ⇒ true
    | S (y:star) ⇒ false]
  | S (x:star) ⇒
    match m with
    [ One ⇒ true
    | S (y:star) ⇒ ge_star_bool x y]  
  ].
let rec ge_bool (n:int) (m:int) on n ≝
  match n with
  [ Minus_inf ⇒ 
    match m with
    [ Minus_inf  ⇒ true
    | Minus (x:star) ⇒ false
    | Zero ⇒ false
    | Plus (y:star) ⇒ false
    | Plus_inf ⇒ false
    ]
  | Minus (x:star) ⇒
    match m with
    [ Minus_inf ⇒ true
    | Minus (y:star) ⇒ ge_star_bool y x
    | Zero ⇒ false
    | Plus (z:star) ⇒ false
    | Plus_inf ⇒ false
    ]
  | Zero ⇒
    match m with
    [ Minus_inf ⇒ true
    | Minus (y:star) ⇒ true
    | Zero ⇒ true
    | Plus (z:star) ⇒ false
    | Plus_inf ⇒ false
    ]
  | Plus (y:star) ⇒
    match m with
    [ Minus_inf ⇒ true
    | Minus (z:star) ⇒ true
    | Zero ⇒ true
    | Plus (w:star) ⇒ ge_star_bool y w
    | Plus_inf ⇒ false
    ]
  | Plus_inf ⇒ true
  ].

axiom ge_bool_prop: ∀x,y:int. ge_bool x y=true → ge_prop x y.

theorem test00: ∀x,y:int. le_prop x y → ge_prop y x.
  assume x:int
  assume y:int
  we proceed by induction on x to prove  (le_prop x y→ge_prop y x)
  case Minus_inf
    we need to prove  (le_prop Minus_inf y→ge_prop y Minus_inf)
    that is equivalent to  (True→ge_prop y Minus_inf)
    suppose (True) (T)
    we need to prove  (∀z:int. ge_prop z Minus_inf) (KK)
      assume z:int
      
    
  
  
  
  
  
  
  
  
  
  
  
  
  
