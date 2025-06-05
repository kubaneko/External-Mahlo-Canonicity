module IR where

open import Data.Bool
open import Data.Empty
open import Data.Nat
open import Data.Product renaming (proj₁ to ₁; proj₂ to ₂)
open import Data.Unit
open import Function
open import Data.Irrelevant

Fam : Set₁
Fam = Σ Set λ A → A → Set

module Step (AB : Fam) where
  A = ₁ AB
  B = ₂ AB

  mutual
    data U : Set where
      A'     : U
      B'     : A → U
      ℕ' 0'  : U
      Π' Σ'  : (A : U) → (El A → U) → U

    El : U → Set
    El A'        = A
    El (B' x)    = B x
    El ℕ'        = ℕ
    El 0'        = ⊥
    El (Π' A B)  = (a : El A) → El (B a)
    El (Σ' A B)  = Σ (El A) (El ∘ B)

  UEl : Fam
  UEl = U , El

UEl : ℕ → Fam
UEl zero     = Step.UEl (⊥ , λ ())
UEl (suc n)  = Step.UEl (UEl n)

U : ℕ → Set
U n = ₁ (UEl n)

El : ∀ {n} → U n → Set
El {n} = ₂ (UEl n )
