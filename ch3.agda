data ⊤ : Set where
  tt : ⊤

data ⊥ : Set where

absurd : {A : Set} → ⊥ → A
absurd ()

data Bool : Set where
  true  : Bool
  false : Bool

data _×_ (A B : Set) : Set where
  _,_ : A → B → A × B
infixr 4 _,_

fst : {A B : Set} → A × B → A
fst (x , y) = x

snd : {A B : Set} → A × B → B
snd (x , y) = y

data Either (A B : Set) : Set where
  left : A → Either A B
  right : B → Either A B

ex1 : {A B : Set} → A → (B → A)
ex1 a = λ b → a

ex2 : {A : Set} → A × ⊤ → Either A ⊥
ex2 (a , t) = left a

ex3 : {A B C : Set} → (A → (B → C)) → (A × B → C)
ex3 f (a , b) = (f a) b

ex4 : {A B C : Set} → A × (Either B C) → Either (A × B) (A × C)
ex4 (a , left b) = left (a , b)
ex4 (a , right c) = right (a , c)

ex5 : {A B C D : Set} → (A → C) → (B → D) → (A × B) → (C × D)
ex5 f g (a , b) = (f a , g b)

cases : {A B C : Set} → Either A B → (A → C) → (B → C) → C
cases (left a) f g = f a
cases (right b) f g = g b

proof1 : {P : Set} → P → P
proof1 p = p

proof2 : {P Q R : Set} → (P → Q) × (Q → R) → (P → R)
proof2 (f , g) = λ x → g (f x)

proof3 : {P Q R : Set} → (Either P Q → R) → (P → R) × (Q → R)
proof3 f = (λ x → f (left x)) , (λ y → f (right y))

doubleNeg : {P : Set} → (Either P (P → ⊥) → ⊥) → ⊥
doubleNeg f = f (right (λ p → f (left p)))

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

data IsEven : ℕ → Set where
  zeroIsEven : IsEven zero
  sucsucIsEven : {n : ℕ} → IsEven n → IsEven (suc (suc n))

6IsEven : IsEven 6
6IsEven = sucsucIsEven (sucsucIsEven (sucsucIsEven zeroIsEven))

1IsNotEven : IsEven 1 → ⊥
1IsNotEven ()

7IsNotEven : IsEven 7 → ⊥
7IsNotEven (sucsucIsEven (sucsucIsEven (sucsucIsEven ())))

data IsTrue : Bool → Set where
  TrueIsTrue : IsTrue true

_=Nat_ : ℕ → ℕ → Bool
zero    =Nat zero    = true
(suc x) =Nat (suc y) = x =Nat y
_       =Nat _       = false

data Σ (A : Set) (B : A → Set) : Set where
  _,_ : (x : A) → B x → Σ A B

double : ℕ → ℕ
double zero    = zero
double (suc n) = suc (suc (double n))

doubleIsEven : (n : ℕ) → IsEven (double n)
doubleIsEven zero    = zeroIsEven
doubleIsEven (suc m) = sucsucIsEven(doubleIsEven m)

nEqualsn : (n : ℕ) → IsTrue (n =Nat n)
nEqualsn zero = TrueIsTrue
nEqualsn (suc m) = nEqualsn m

zeroOrSuc : (n : ℕ) → Either (IsTrue (n =Nat 0))
                             (Σ ℕ (λ m → IsTrue (n =Nat (suc m))))
zeroOrSuc zero    = left TrueIsTrue
zeroOrSuc (suc m) = right (m , nEqualsn (suc m))

data _≡_ {A : Set} : A → A → Set where
  refl : {x : A} → x ≡ x
infix 4 _≡_

onePlusOne : (suc (suc zero)) ≡ 2
onePlusOne = refl

zeroNotOne : 0 ≡ 1 → ⊥
zeroNotOne ()

id : {A : Set} → A → A
id x = x

idReturnsInput : {A : Set} → (x : A) → id x ≡ x
idReturnsInput x = refl

sym : {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl

cong : {A B : Set} {x y : A} → (f : A → B) → x ≡ y → f x ≡ f y
cong f refl = refl
