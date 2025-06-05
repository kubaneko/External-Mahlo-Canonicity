module MahloDerivations where

open import Relation.Binary.PropositionalEquality
open import Data.Nat
open import Function
open import Data.Unit
open import Data.Empty
open import Data.Bool
open import Data.Product renaming (proj₁ to ₁; proj₂ to ₂)
open import Data.Irrelevant

module Doel
    (U+  : (A : Set) → (B : A → Set) → Set)
    (El+ : (A : Set) → (B : A → Set) → U+ A B → Set) where

  data Ma : Set
  El : Ma → Set

  data Ma where
    ℕ' 0' : Ma
    Π'    : (a : Ma) → (b : El a → Ma) → Ma
    U+'   : (a : Ma) → (b : El a → Ma) → Ma
    El+'  : (a : Ma) → (b : El a → Ma) → U+ (El a) (El ∘ b) → Ma

  El ℕ'            = ℕ
  El 0'            = ⊥
  El (Π' a b)      = (x : El a) → El (b x)
  El (U+' a b)     = U+ (El a) (El ∘ b)
  El (El+' a b x)  = El+ (El a) (El ∘ b) x

  MaElim : (P   : Ma → Set)
        → (n    : P ℕ')
        → (z    : P 0')
        → (pi   : ∀ a → P a → ∀ b → (∀ x → P (b x)) → P (Π' a b))
        → (u+   : ∀ a → P a → ∀ b → (∀ x → P (b x)) → P (U+' a b))
        → (el+  : (a : Ma) → P a → (b : El a → Ma) → (∀ x → P (b x))
                      → (x : U+ (El a) (El ∘ b)) → P (El+' a b x))
        → (u : Ma) → P u
  MaElim P n z pi u+ el+ ℕ'            = n
  MaElim P n z pi u+ el+ 0'            = z
  MaElim P n z pi u+ el+ (Π' a b)      =
    pi a (MaElim P n z pi u+ el+ a) b (MaElim P n z pi u+ el+ ∘ b)
  MaElim P n z pi u+ el+ (U+' a b)     =
    u+ a (MaElim P n z pi u+ el+ a) b (MaElim P n z pi u+ el+ ∘ b)
  MaElim P n z pi u+ el+ (El+' a b x)  =
    el+ a (MaElim P n z pi u+ el+ a) b (MaElim P n z pi u+ el+ ∘ b) x


module Mahlo
    (U0  : Set)
    (El0 : U0 → Set)
    (U+  : (A : Set) → (B : A → Set) → Set)
    (El+ : (A : Set) → (B : A → Set) → U+ A B → Set) where

  data Ma : Set
  El : Ma → Set

  data Ma where
    El0' : U0 → Ma
    El+' : (a : Ma) → (b : El a → Ma) → U+ (El a) (El ∘ b) → Ma

  El (El0' u)      = El0 u
  El (El+' a b x)  = El+ (El a) (El ∘ b) x

  MaElim : (P   : Ma → Set)
        → (el0 : ∀ x → P (El0' x))
        → (el+ : (a : Ma) → P a → (b : El a → Ma) → (∀ x → P (b x))
                     → (x : U+ (El a) (El ∘ b)) → P (El+' a b x))
        → (u : Ma) → P u
  MaElim P el0 el+ (El0' x)      = el0 x
  MaElim P el0 el+ (El+' a b x)  = el+ a (MaElim P el0 el+ a)
                                       b (MaElim P el0 el+ ∘ b) x

module Translation
  (U+  : (A : Set) → (B : A → Set) → Set)
  (El+ : (A : Set) → (B : A → Set) → U+ A B → Set) where

  data U0* : Set where
    ℕ'* 0'* : U0*

  El0* : U0* → Set
  El0* ℕ'* = ℕ
  El0* 0'* = ⊥

  data U+* (A : Set) (B : A → Set) : Set where
    Π'*    : U+* A B
    U'+*   : U+* A B
    El+'*  : U+ A B → U+* A B

  El+* : (A : Set) → (B : A → Set) → U+* A B → Set
  El+* A B Π'*        = ∀ a → B a
  El+* A B U'+*       = U+ A B
  El+* A B (El+'* x)  = El+ A B x

  module M = Mahlo U0* El0* U+* El+*

  Ma : Set
  Ma = M.Ma

  El : Ma → Set
  El = M.El

  ℕ' : Ma
  ℕ' = M.El0' ℕ'*

  0' : Ma
  0' = M.El0' 0'*

  Π' : (a : Ma) → (b : El a → Ma) → Ma
  Π' a b = M.El+' a b Π'*

  U+' : (a : Ma) → (b : El a → Ma) → Ma
  U+' a b = M.El+' a b U'+*

  El+' : (a : Ma) → (b : El a → Ma) → U+ (El a) (El ∘ b) → Ma
  El+' a b x = M.El+' a b (El+'* x)

  Elℕ'    : El ℕ'                        ≡ ℕ
  El0'    : El 0'                        ≡ ⊥
  ElΠ'    : ∀ {a b} → El (Π' a b)        ≡ ((x : El a) → El (b x))
  ElU+'   : ∀ {a b} → El (U+' a b)       ≡ U+ (El a) (El ∘ b)
  ElEl+'  : ∀ {a b x} → El (El+' a b x)  ≡ El+ (El a) (El ∘ b) x
  Elℕ'    = refl
  El0'    = refl
  ElΠ'    = refl
  ElU+'   = refl
  ElEl+'  = refl

  MaElim : (P    : Ma → Set)
         → (n    : P ℕ')
         → (z    : P 0')
         → (pi   : ∀ a → P a → ∀ b → (∀ x → P (b x)) → P (Π' a b))
         → (u+   : ∀ a → P a → ∀ b → (∀ x → P (b x)) → P (U+' a b))
         → (el+  : (a : Ma) → P a → (b : El a → Ma) → (∀ x → P (b x))
                       → (x : U+ (El a) (El ∘ b)) → P (El+' a b x))
         → (u : Ma) → P u
  MaElim P n z pi u+ el+ = M.MaElim
    P
    (λ { ℕ'* → n ; 0'* → z})
    (λ { a pa b pb Π'*       → pi a pa b pb ;
         a pa b pb U'+*      → u+ a pa b pb ;
         a pa b pb (El+'* x) → el+ a pa b pb x})

  MaElimℕ'   : ∀ {P n z pi u+ el+} → MaElim P n z pi u+ el+ ℕ' ≡ n
  MaElim0'   : ∀ {P n z pi u+ el+} → MaElim P n z pi u+ el+ 0' ≡ z
  MaElimΠ'   : ∀ {P n z pi u+ el+ a b}
    → MaElim P n z pi u+ el+ (Π' a b)     ≡
        pi a (MaElim P n z pi u+ el+ a) b (MaElim P n z pi u+ el+ ∘ b)
  MaElimU+'  : ∀ {P n z pi u+ el+ a b  }
    → MaElim P n z pi u+ el+ (U+' a b)    ≡
        u+ a (MaElim P n z pi u+ el+ a) b (MaElim P n z pi u+ el+ ∘ b)
  MaElimEl+' : ∀ {P n z pi u+ el+ a b x}
    → MaElim P n z pi u+ el+ (El+' a b x) ≡
        el+ a (MaElim P n z pi u+ el+ a)
            b (MaElim P n z pi u+ el+ ∘ b) x
  MaElimℕ'    = refl
  MaElim0'    = refl
  MaElimΠ'    = refl
  MaElimU+'   = refl
  MaElimEl+'  = refl


module Example where
  Fam : Set₁
  Fam = Σ Set λ A → A → Set


  module Step (AB : Fam) where
    A = ₁ AB
    B = ₂ AB

    data U0 : Set where
      A'           : U0
      B'           : A → U0
      0' 1' 2' ℕ'  : U0

    El0 : U0 → Set
    El0 A'      = A
    El0 (B' x)  = B x
    El0 0'      = ⊥
    El0 1'      = ⊤
    El0 2'      = Bool
    El0 ℕ'      = ℕ

    data U+ (A : Set)(B : A → Set) : Set where
      Π' : U+ A B
      Σ' : U+ A B

    El+ : (A : Set) → (B : A → Set) → U+ A B → Set
    El+ A B Π' = (x : A) → B x
    El+ A B Σ' = Σ A B

    UEl : Fam
    UEl = Mahlo.Ma U0 El0 U+ El+ ,
          Mahlo.El U0 El0 U+ El+

  UEl : ℕ → Fam
  UEl zero     = Step.UEl (⊥ , λ ())
  UEl (suc n)  = Step.UEl (UEl n)

  U : ℕ → Set
  U n = ₁ (UEl n)

  El : ∀ {n} → U n → Set
  El {n} = ₂ (UEl n)
