{-# OPTIONS --allow-unsolved-metas #-}
open import Data.List.Relation.Unary.Unique.Propositional.Properties using (map⁺; drop⁺)

open import Prelude.Init
open import Prelude.Lists
open import Prelude.DecEq
open import Prelude.Set'

open import Language

module NFA (Σ : Alphabet) where

record NFA (S : Type) {{_ : DecEq S}} : Type where
  field
    Q  : Set⟨ S ⟩
    -- Σ  : Alphabet
    δ  : S → Token → Set⟨ S ⟩
    Q₀ : ∃ (_∈′ Q)
    -- q₀ : S
    -- q₀∈
    F  : ∃ (_⊆′ Q)

  q₀ = proj₁ Q₀
  fs = proj₁ F

  isFinal : S → Type
  isFinal = _∈′ fs

  isFinal? : Decidable¹ isFinal
  isFinal? = _∈′? fs

  Δ : S → Word → Set⟨ S ⟩
  Δ s ε       = singleton s
  Δ s (α ∷ w) = ⋃ (flip Δ w) (δ s α)

  δ̂ : Word → Set⟨ S ⟩
  δ̂ = Δ q₀

open NFA public

instance
  L-NFA : ∀ {S} {{_ : DecEq S}} → Language (NFA S)
  L-NFA .accept nfa@(record {F = F , _}) w =
    (δ̂ nfa w ∩ F) ≢ ∅
    -- count′ (isFinal? nfa) (δ̂ nfa w) > 0

open import DFA Σ as D
  hiding (δ̂)

{-# TERMINATING #-}
ℙ : ∀ {S} {{_ : DecEq S}} → Set⟨ S ⟩ → Set⟨ Set⟨ S ⟩ ⟩
ℙ {S} (⟨ []     ⟩∶- _) = singleton ∅
ℙ {S} (⟨ x ∷ xs ⟩∶- p) =
  let xss = ℙ (⟨ xs ⟩∶- drop⁺ 1 p)
  in  xss ∪ (cons <$> xss ∶- inj)
    where
      cons : Set⟨ S ⟩ → Set⟨ S ⟩
      cons xs = x ∷ xs ∶- {!!}

      inj : (∀ {xs ys} → cons xs ≡ cons ys → xs ≡ ys)
      inj = {!!}

NFA⇒DFA : ∀ {S} {{_ : DecEq S}} → (nfa : NFA S) → Σ[ dfa ∈ DFA Set⟨ S ⟩ ] (nfa ~ dfa)
NFA⇒DFA {S = S} nfa@(record { Q = Q ; δ = δ ; Q₀ = q₀ , _ ; F = F , _ }) =
  dfa , nfa~dfa
  where
    δᵈ : Set⟨ S ⟩ → Token → Maybe Set⟨ S ⟩
    δᵈ s α = just $ ⋃ (flip δ α) s

    dfa : DFA Set⟨ S ⟩
    dfa = record { Q = ℙ Q ; δ = δᵈ ; Q₀ = singleton q₀ , {!!} ; F = filter′ (any? (_∈′? F) ∘ list) (ℙ Q) , {!!} }

    nfa~dfa : nfa ~ dfa
    nfa~dfa w = {!!}
    {-
      with w     | δ̂ nfa w        | D.δ̂ dfa w
    ... | ε      | ⟨ q ∷ [] ⟩∶- _ | just (⟨ q′ ∷ [] ⟩∶- _)
                  -- ^ q = q′ = q₀ ??
    ... | (α ∷ w | ??             | ??
        = {!!}
    -}

      -- p₁ , p₂
      -- where
      --   p₁ : accept nfa w → accept dfa w
      --   p₁ = {!!}

      --   p₂ : accept dfa w → accept nfa w
      --   p₂ = {!!}
