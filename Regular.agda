open import Induction.WellFounded
open import Data.Nat.Induction using (<-wellFounded)
open import Data.Nat.Properties

open import Prelude.Init
open import Prelude.Lists
open import Prelude.DecEq
open import Prelude.Set'
open import Prelude.Bifunctor
open import Prelude.Applicative
open import Prelude.Semigroup
open import Prelude.Nary

open import Language

module Regular (Σ : Alphabet) where

data Regex : Type where
  `∅ : Regex

  `ε : Regex

  I : (a : Token) → a ∈′ Σ → Regex

  _`∪_ : Regex → Regex → Regex

  _∙_ : Regex → Regex → Regex

  _⁺ : Regex → Regex

  {- _⋆ : Regex → Regex -}

⋃_ : List Regex → Regex
⋃_ = foldr _`∪_ `∅

∀Σ : Regex
∀Σ = ⋃ mapWith∈ (list Σ) (I _)

len : ℕ → Regex
len 0 = `ε
len (suc n) = len n ∙ ∀Σ

_⁇ : Regex → Regex
g ⁇ = `ε `∪ g

_⋆ : Regex → Regex
g ⋆ = (g ⁺) ⁇

{-
_⁺ : Regex → Regex
g ⁺ = g ∙ (g ⋆)
-}

infixr 8 _∙_
infixr 7 _`∪_

_≺_ : Rel Word 0ℓ
_≺_ = _<_ on length

≺-wf : WellFounded _≺_
≺-wf = InverseImage.wellFounded length <-wellFounded

+-≺ : ∀ {x y z} → suc x + y ≡ z → y < z
+-≺ {x}{y}{z} refl = <-transˡ {i = y} {j = suc y} {k = suc x + y} (n<1+n y) (s≤s $ m≤n+m y x)

private
  variable
    g g′ : Regex

data Accept : Regex → Word → Type where

  [ε]  : Accept `ε ε

  [I]  : ∀ {x x∈} → Accept (I x x∈) [ x ]

  [∪ˡ] : ∀ {g g′ w} → Accept g w → Accept (g `∪ g′) w

  [∪ʳ] : ∀ {g g′ w} → Accept g w → Accept (g′ `∪ g) w

  [∙]  : ∀ {w w′ g g′} → Accept g w → Accept g′ w′ → Accept (g ∙ g′) (w ++ w′)

{-
  [⋆-base] : Accept (g ⋆) ε
  [⋆-step] : ∀ {w w′ g} → Accept g w → Accept (g ⋆) w′ → Accept (g ⋆) (w ++ w′)
-}

  [⁺]  : ∀ {w w′ g} → Accept g w → Accept (g ⋆) w′ → Accept (g ⁺) (w ++ w′)

_∈ʳ_ = Accept

instance
  L-Regex : Language Regex
  L-Regex .accept = Accept
  {- g w = go g _ (≺-wf w)
   where
    go : Regex → (w : Word) → Acc _≺_ w → Type
    go g w a₀@(acc a)
      with g
    ... | `∅       = ⊥
    ... | `ε       = w ≡ ε
    ... | I x _    = w ≡ [ x ]
    ... | g₁ `∪ g₂ = go g₁ w a₀ ⊎ go g₂ w a₀
    ... | g₁ ∙ g₂  = Σ[ i ∈ Fin (suc $ length w) ]
          let wˡ , wʳ = splitAt w i
          in go g₁ wˡ (≺-wf wˡ) × go g₂ wʳ (≺-wf wʳ)
    ... | g′ ⁺     = Σ[ i ∈ Index w ]
          let wˡ⁺ , wʳ , p = splitAt⁺ʳ w i
              wˡ = L.NE.toList wˡ⁺
          in  go g′ wˡ (≺-wf wˡ) ×
              ( go `ε wʳ (a _ (+-≺ p))
              ⊎ go (g′ ⁺) wʳ (a _ (+-≺ p)) ) -}

              -- go (`ε `∪ (g′ ⁺)) wʳ (a _ (+-≺ p))
              -- go (g′ ⋆) wʳ (a _ (+-≺ p))
            -- NB: Agda fails termination checking if we do not inline _`∪_

{- _ : Decidable _∈ʳ_
-}
