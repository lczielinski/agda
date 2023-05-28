data Nat : Set where
  zero : Nat
  suc  : Nat → Nat

{-# BUILTIN NATURAL Nat #-}

_+_ : Nat → Nat → Nat
zero    + y = y
(suc x) + y = suc (x + y)

data Bool : Set where
  true  : Bool
  false : Bool

not : Bool → Bool
not true  = false
not false = true

data Vec (A : Set) : Nat → Set where
  []   : Vec A 0
  _::_ : {n : Nat} → A → Vec A n → Vec A (suc n)
infixr 5 _::_

myVec1 : Vec Nat 5
myVec1 = 1 :: 2 :: 3 :: 4 :: 5 :: []

myVec2 : Vec (Bool → Bool) 2
myVec2 = not :: (λ x → x) :: []

zeroes : (n : Nat) → Vec Nat n
zeroes zero    = []
zeroes (suc n) = 0 :: zeroes n

downFrom : (n : Nat) → Vec Nat n
downFrom zero = []
downFrom (suc n) = n :: downFrom n

prepend : {n : Nat} → Bool → Vec Bool n → Vec Bool (suc n)
prepend b bs = b :: bs

_++Vec_ : {A : Set} {m n : Nat} → Vec A m → Vec A n → Vec A (m + n)
[] ++Vec ys = ys
(x :: xs) ++Vec ys = x :: (xs ++Vec ys)

head : {A : Set} {n : Nat} → Vec A (suc n) → A
head (x :: xs) = x

tail : {A : Set} {n : Nat} → Vec A (suc n) → Vec A n
tail (x :: xs) = xs

data Fin : Nat → Set where
  zero : {n : Nat} → Fin (suc n)
  suc  : {n : Nat} → Fin n → Fin (suc n)

lookupVec : {A : Set} {n : Nat} → Vec A n → Fin n → A
lookupVec (x :: xs) zero = x
lookupVec (x :: xs) (suc i) = lookupVec xs i

putVec : {A : Set} {n : Nat} → Fin n → A → Vec A n → Vec A n
putVec zero a (x :: xs) = a :: xs
putVec (suc i) a (x :: xs) = x :: putVec i a xs

data Σ (A : Set) (B : A → Set) : Set where
  _,_ : (x : A) → B x → Σ A B

data _×_ (A B : Set) : Set where
  _,_ : A → B → A × B
infixr 4 _,_

_×'_ : (A B : Set) → Set
A ×' B = Σ A (λ _ → B)

fstΣ : {A : Set} {B : A → Set} → Σ A B → A
fstΣ (x , y) = x

sndΣ : {A : Set} {B : A → Set} → (z : Σ A B) → B (fstΣ z)
sndΣ (x , y) = y

List' : (A : Set) → Set
List' A = Σ Nat (Vec A)
