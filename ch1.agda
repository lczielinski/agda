data Greeting : Set where
  hello : Greeting

greet : Greeting
greet = hello

data Nat : Set where
  zero : Nat
  suc  : Nat → Nat

{-# BUILTIN NATURAL Nat #-}

_+_ : Nat → Nat → Nat
zero    + y = y
(suc x) + y = suc (x + y)

halve : Nat → Nat
halve zero          = zero
halve (suc zero)    = zero
halve (suc (suc x)) = suc (halve x)

_*_ : Nat → Nat → Nat
zero * y    = zero
(suc x) * y = y + (x * y)

data Bool : Set where
  true  : Bool
  false : Bool

not : Bool → Bool
not true  = false
not false = true

_&&_ : Bool → Bool → Bool
true && true = true
_ && _       = false

id : {A : Set} → A → A
id x = x

if_then_else_ : {A : Set} → Bool → A → A → A
if true then x else y  = x
if false then x else y = y

data List (A : Set) : Set where
  []   : List A
  _::_ : A → List A → List A
infixr 5 _::_

data _×_ (A B : Set) : Set where
  _,_ : A → B → A × B
infixr 4 _,_

fst : {A B : Set} → A × B → A
fst (x , y) = x

snd : {A B : Set} → A × B → B
snd (x , y) = y

length : {A : Set} → List A → Nat
length []        = 0
length (x :: xs) = 1 + (length xs)

_++_ : {A : Set} → List A → List A → List A
[]        ++ back = back
(x :: xs) ++ back = x :: (xs ++ back)

map : {A B : Set} → (A → B) → List A → List B
map f []        = []
map f (x :: xs) = (f x) :: (map f xs)

data Maybe (A  : Set) : Set where
  just    : A → Maybe A
  nothing : Maybe A

lookup : {A : Set} → List A → Nat → Maybe A
lookup [] _              = nothing
lookup (x :: xs) zero    = just x
lookup (x :: xs) (suc i) = lookup xs i
