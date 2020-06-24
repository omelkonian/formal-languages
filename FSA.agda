{-# OPTIONS --allow-unsolved-metas #-}
open import Language

module FSA (Σ : Alphabet) where

record FSA (S : Type) {{_ : DecEq S}} : Type where
  field
    Q  : Set⟨ S ⟩
    -- Σ  : Alphabet
    δ  : S × Token → Maybe S
    Q₀ : ∃ (_∈′ Q)
    -- q₀ : S
    -- q₀∈
    F  : ∃ (_⊆′ Q)

  q₀ = proj₁ Q₀
  fs = proj₁ F

  δ̂ : Word → Maybe S
  δ̂ = go q₀
    where
      go : S → Word → Maybe S
      go s ε       = just s
      go s (t ∷ w) with δ (s , t)
      ... | nothing = nothing
      ... | just s′ = go s′ w

open FSA public

-- Example FSA
-- _ : FSA 0|1
-- _ = ?

∁ : ∀ {S} {{_ : DecEq S}} → FSA S → FSA S
∁ record {Q = Q; δ = δ; Q₀ = Q₀; F = (F , F⊆)} =
  record {Q = Q; δ = δ; Q₀ = Q₀; F = (Q ─ F , ∈-─ {xs = Q} {ys = F})}

instance
  L-FSA : ∀ {S} {{_ : DecEq S}} → Language (FSA S)
  L-FSA .accept fsa w = ∃ λ s → (δ̂ fsa w ≡ just s) × (s ∈′ fs fsa)


-- To/from Regex
open import Regular Σ

DFA⇒Regex : ∀ {S} {{_ : DecEq S}} → FSA S → Regex
DFA⇒Regex {S = S} record { Q = Q ; δ = δ ; Q₀ = Q₀@(q₀ , _) ; F = F@(fs , _) } =
  ⋃ map (R (#_ ∣ Q ∣ {m<n = {!!}}) q₀) (list fs)
  where
    R : Fin (suc ∣ Q ∣) → S → S → Regex
    R = {!!}

{-
  -- Stage 0
  R⁰


  -- Stage 1
  R¹


  -- Stage 2
  R²




  ⋮


  -- Stage n
  Rⁿ

  ⇒ Rⁿ(q₀↦f₀) ∪ Rⁿ(q₀↦f₁) ∪ ⋯
-}
