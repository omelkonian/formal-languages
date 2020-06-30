module Examples where

open import Prelude.Init
open import Prelude.Set'
open import Prelude.DecEq
open import Prelude.Applicative
open import Prelude.Semigroup
open import Prelude.Nary
open import Language

module Regex-Example where
  open import Regular (fromList ⟦ '0' , '1' ⟧)

  G⁰ : Regex
  G⁰ = I '0' (here refl)

  G¹ : Regex
  G¹ = I '1' (there (here refl))

  -- (0 | 1((01)⋆0)⋆1)⋆ : binary numbers that are multiples of 3
  Bin3 : Regex
  Bin3 = ( G⁰
        `∪ (G¹ ∙ ((((G⁰ ∙ G¹) ⋆) ∙ G⁰) ⋆) ∙ G¹)
         ) ⋆

  _ : accept Bin3 ⟦ '0' , '0' , '1' , '1' , '0' ⟧
  _ = [∪ʳ] ([⁺] ([∪ˡ] [I])
                ([∪ʳ] ([⁺] ([∪ˡ] [I])
                           ([∪ʳ] ([⁺] ([∪ʳ] ([∙] [I] ([∙] ([∪ˡ] [ε]) [I])))
                                      ([∪ʳ] ([⁺] ([∪ˡ] [I]) ([∪ˡ] [ε]))))))))

module FSA-Example where
  open import Regular (singleton 'a')
  open import FSA     (singleton 'a')

  α⋆ : FSA ℕ
  Q  α⋆ = singleton 1
  δ  α⋆ = λ{ 1 'a' → just 1
          ; _ _   → nothing }
  Q₀ α⋆ = 1 , here refl
  F  α⋆ = singleton 1 , λ{ (here refl) → here refl; (there ()) }

  {-# DISPLAY I a b = a #-}
  {-# DISPLAY _`∪_ a b = a ∪ b #-}
  {-# DISPLAY `∅ = ∅ #-}
  {-# DISPLAY `ε = ε #-}

  -- _ : ⊤
  -- _ = {!!}
  -- ^ Ctrl+n: proj₁ (DFA⇒Regex α⋆)

{-
-- | e? ∙ e⁺ ↝ e⋆
-- | e ∙ e⋆ ↝ e⁺
-- | e? ∙ e⁺ → e⋆
-- | ε ∪ a ∪ a⋆
   ⇒ ε ∪ a⋆
   ⇒ a⋆

-- a? ∪ (a? ∙ a?⋆ ∙ a?)
-- a? ∪ (a⋆ ∙ a?)
-- a? ∪ a⋆
-- a⋆
-}
