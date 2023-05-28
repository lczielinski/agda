data _≡_ {A : Set} : A → A → Set where
  refl : {x : A} → x ≡ x
infix 4 _≡_

sym : {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl

cong : {A B : Set} {x y : A} → (f : A → B) → x ≡ y → f x ≡ f y
cong f refl = refl

begin_ : {A : Set} → {x y : A} → x ≡ y → x ≡ y
begin p = p

_end : {A : Set} → (x : A) → x ≡ x
x end = refl

_=⟨_⟩_ : {A : Set} → (x : A) → {y z : A} → x ≡ y → y ≡ z → x ≡ z
x =⟨ p ⟩ q = trans p q

_=⟨⟩_ : {A : Set} → (x : A) → {y : A} → x ≡ y → x ≡ y
x =⟨⟩ q = x =⟨ refl ⟩ q

infix  1 begin_
infix  3 _end
infixr 2 _=⟨_⟩_
infixr 2 _=⟨⟩_

data List (A : Set) : Set where
  []   : List A
  _::_ : A → List A → List A
infixr 5 _::_

_++_ : {A : Set} → List A → List A → List A
[]        ++ back = back
(x :: xs) ++ back = x :: (xs ++ back)

[_] : {A : Set} → A → List A
[ x ] = x :: []

reverse : {A : Set} → List A → List A
reverse [] = []
reverse (x :: xs) = reverse xs ++ [ x ]

reverse-singleton : {A : Set} (x : A) → reverse [ x ] ≡ [ x ]
reverse-singleton x =
  begin
    reverse [ x ]
  =⟨⟩
    reverse (x :: [])
  =⟨⟩
    reverse [] ++ [ x ]
  =⟨⟩
    [ x ]
  end

data Bool : Set where
  true  : Bool
  false : Bool

not : Bool → Bool
not true  = false
not false = true

notNot : (b : Bool) → not (not b) ≡ b
notNot false =
  begin
    not (not false)
  =⟨⟩
    not true
  =⟨⟩
    false
  end
notNot true =
  begin
    not (not true)
  =⟨⟩
    not false
  =⟨⟩
    true
  end

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

_+_ : ℕ → ℕ → ℕ
zero    + y = y
(suc x) + y = suc (x + y)

addNZero : (n : ℕ) → n + zero ≡ n
addNZero zero =
  begin
    zero + zero
  =⟨⟩
    zero
  end
addNZero (suc n) =
  begin
    (suc n) + zero
  =⟨⟩
    suc (n + zero)
  =⟨ cong suc (addNZero n) ⟩ -- provide proof
    suc n
  end

ex4-1 : (m n : ℕ) → m + suc n ≡ suc (m + n)
ex4-1 zero n =
  begin
    zero + suc n
  =⟨⟩
    suc n
  =⟨⟩
    suc (zero + n)
  end
ex4-1 (suc k) n =
  begin
    (suc k) + suc n
  =⟨⟩
    suc (k + suc n)
  =⟨ cong suc (ex4-1 k n) ⟩
    suc (suc (k + n))
  =⟨⟩
    suc ((suc k) + n)
  end
  
addAssoc : (x y z : ℕ) → x + (y + z) ≡ (x + y) + z
addAssoc zero y z =
  begin
    zero + (y + z)
  =⟨⟩
    y + z
  =⟨⟩
    (zero + y) + z
  end
addAssoc (suc x) y z =
  begin
    (suc x) + (y + z)
  =⟨⟩
    suc (x + (y + z))
  =⟨ cong suc (addAssoc x y z) ⟩
    suc ((x + y) + z)
  =⟨⟩
    (suc (x + y)) + z
  =⟨⟩
    ((suc x) + y) + z
  end

length : {A : Set} → List A → ℕ
length []        = 0
length (x :: xs) = 1 + (length xs)

replicate : {A : Set} → ℕ → A → List A
replicate zero    x = []
replicate (suc n) x = x :: replicate n x

ex4-2 : {A : Set} → (n : ℕ) (x : A) → length (replicate n x) ≡ n
ex4-2 zero x =
  begin
    length (replicate zero x)
  =⟨⟩
    zero
  end
ex4-2 (suc n) x =
  begin
    length (replicate (suc n) x)
  =⟨⟩
    length (x :: replicate n x)
  =⟨⟩
    1 + (length (replicate n x))
  =⟨ cong suc (ex4-2 n x) ⟩
    1 + n
  =⟨⟩
    suc n
  end

append-[] : {A : Set} → (xs : List A) → xs ++ [] ≡ xs
append-[] [] = refl
append-[] (x :: xs) =
  begin
    (x :: xs) ++ []
  =⟨⟩
    x :: (xs ++ [])
  =⟨ cong (x ::_) (append-[] xs) ⟩
    x :: xs
  end

appendAssoc : {A : Set} → (xs ys zs : List A)
            → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
appendAssoc [] ys zs =
  begin
    ([] ++ ys) ++ zs
  =⟨⟩
    ys ++ zs
  =⟨⟩
    [] ++ (ys ++ zs)
  end
appendAssoc (x :: xs) ys zs =
  begin
     ((x :: xs) ++ ys) ++ zs
  =⟨⟩
     (x :: (xs ++ ys)) ++ zs
  =⟨⟩
     x :: ((xs ++ ys) ++ zs)
  =⟨ cong (x ::_) (appendAssoc xs ys zs) ⟩
     x :: (xs ++ (ys ++ zs))
  =⟨⟩
     (x :: xs) ++ (ys ++ zs)
  end

reverseReverse : {A : Set} → (xs : List A) → reverse (reverse xs) ≡ xs
reverseReverse [] =
  begin
    reverse (reverse [])
  =⟨⟩
    reverse []
  =⟨⟩
    []
  end
reverseReverse (x :: xs) =
  begin
    reverse (reverse (x :: xs))
  =⟨⟩
    reverse (reverse xs ++ [ x ])
  =⟨ reverseDist (reverse xs) [ x ] ⟩
    reverse [ x ] ++ reverse (reverse xs)
  =⟨⟩
    [ x ] ++ reverse (reverse xs)
  =⟨⟩
    x :: reverse (reverse xs)
  =⟨ cong (x ::_) (reverseReverse xs) ⟩
    x :: xs
  end
  where
    reverseDist : {A : Set} → (xs ys : List A)
                → reverse (xs ++ ys) ≡ reverse ys ++ reverse xs
    reverseDist [] ys =
      begin
        reverse ([] ++ ys)
      =⟨⟩
        reverse ys
      =⟨ sym (append-[] (reverse ys)) ⟩
        reverse ys ++ []
      =⟨⟩
        reverse ys ++ reverse []
      end
    reverseDist (x :: xs) ys =
      begin
        reverse ((x :: xs) ++ ys)
      =⟨⟩
        reverse (x :: (xs ++ ys))
      =⟨⟩
        reverse (xs ++ ys) ++ reverse [ x ]
      =⟨⟩
        reverse (xs ++ ys) ++ [ x ]
      =⟨ cong (_++ [ x ]) (reverseDist xs ys) ⟩
        (reverse ys ++ reverse xs) ++ [ x ]
      =⟨ appendAssoc (reverse ys) (reverse xs) [ x ] ⟩
        reverse ys ++ (reverse xs ++ [ x ])
      =⟨⟩
        reverse ys ++ (reverse (x :: xs))
      end

map : {A B : Set} → (A → B) → List A → List B
map f []        = []
map f (x :: xs) = (f x) :: (map f xs)

id : {A : Set} → A → A
id x = x

mapId : {A : Set} (xs : List A) → map id xs ≡ xs
mapId [] = refl
mapId (x :: xs) =
  begin
    map id (x :: xs)
  =⟨⟩
    id x :: map id xs
  =⟨⟩
    x :: map id xs
  =⟨ cong (x ::_) (mapId xs) ⟩
    x :: xs
  end

_∘_ : {A B C : Set} → (B → C) → (A → B) → (A → C)
g ∘ h = λ x → g (h x)

mapCompose : {A B C : Set} (f : B → C) (g : A → B) (xs : List A)
           → map (f ∘ g) xs ≡ map f (map g xs)
mapCompose f g [] = refl
mapCompose f g (x :: xs) =
  begin
    map (f ∘ g) (x :: xs)
  =⟨⟩
    (f ∘ g) x :: map (f ∘ g) xs
  =⟨⟩
    f (g x) :: map (f ∘ g) xs
  =⟨ cong (f (g x) ::_) (mapCompose f g xs) ⟩
    f (g x) :: map f (map g xs)
  =⟨⟩
    map f (g x :: map g xs)
  =⟨⟩
    map f (map g (x :: xs))
  end

ex4-4 : {A B : Set} (f : A → B) (xs : List A)
      → length (map f xs) ≡ length xs
ex4-4 f [] = refl
ex4-4 f (x :: xs) =
  begin
    length (map f (x :: xs))
  =⟨⟩
    length (f x :: map f xs)
  =⟨⟩
    1 + (length (map f xs))
  =⟨ cong (1 +_) (ex4-4 f xs) ⟩
    1 + length xs
  =⟨⟩
    length (x :: xs)
  end

reverseAcc : {A : Set} → List A → List A → List A
reverseAcc []        ys = ys
reverseAcc (x :: xs) ys = reverseAcc xs (x :: ys)

reverse' : {A : Set} → List A → List A
reverse' xs = reverseAcc xs []

reverse'-reverse : {A : Set} → (xs : List A)
                 → reverse' xs ≡ reverse xs
reverse'-reverse xs =
  begin
    reverse' xs
  =⟨⟩
    reverseAcc xs []
  =⟨ reverseAccLemma xs [] ⟩
    reverse xs ++ []
  =⟨ append-[] (reverse xs) ⟩
    reverse xs
  end
  where
    reverseAccLemma : {A : Set} → (xs ys : List A)
                    → reverseAcc xs ys ≡ reverse xs ++ ys
    reverseAccLemma [] ys =
      begin
        reverseAcc [] ys
      =⟨⟩
        ys
      =⟨⟩
        [] ++ ys
      =⟨⟩
        reverse [] ++ ys
      end
    reverseAccLemma (x :: xs) ys =
      begin
        reverseAcc (x :: xs) ys
      =⟨⟩
        reverseAcc xs (x :: ys)
      =⟨ reverseAccLemma xs (x :: ys) ⟩
        reverse xs ++ (x :: ys)
      =⟨⟩
        reverse xs ++ ([ x ] ++ ys)
      =⟨ sym (appendAssoc (reverse xs) [ x ] ys) ⟩
        (reverse xs ++ [ x ]) ++ ys
      =⟨⟩
        reverse (x :: xs) ++ ys
      end

data Tree (A : Set) : Set where
  leaf : A → Tree A
  node : Tree A → Tree A → Tree A

flatten : {A : Set} → Tree A → List A
flatten (leaf x)     = [ x ]
flatten (node t1 t2) = flatten t1 ++ flatten t2

flattenAcc : {A : Set} → Tree A → List A → List A
flattenAcc (leaf x)     xs = x :: xs
flattenAcc (node t1 t2) xs = flattenAcc t1 (flattenAcc t2 xs)

flatten' : {A : Set} → Tree A → List A
flatten' t = flattenAcc t []

data Expr : Set where
  valE : ℕ → Expr
  addE : Expr → Expr → Expr

eval : Expr → ℕ
eval (valE x)     = x
eval (addE e1 e2) = eval e1 + eval e2

data Op : Set where
  PUSH : ℕ → Op
  ADD  : Op

Stack = List ℕ
Code = List Op

exec : Code → Stack → Stack
exec []            s             = s
exec (PUSH x :: c) s             = exec c (x :: s)
exec (ADD :: c)    (m :: n :: s) = exec c (n + m :: s)
exec (ADD :: c)    _             = []

compile' : Expr → Code → Code
compile' (valE x)     c = PUSH x :: c
compile' (addE e1 e2) c = compile' e1 (compile' e2 (ADD :: c))

compile : Expr → Code
compile e = compile' e []
