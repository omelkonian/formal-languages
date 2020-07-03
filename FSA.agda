{-# OPTIONS --allow-unsolved-metas #-}
open import Language

open import Data.Fin using (inject₁)
open import Data.List.Membership.Propositional.Properties

open import Prelude.Init hiding (_⇔_)
open import Prelude.Lists
open import Prelude.DecEq
open import Prelude.Functor
open import Prelude.Set'

module FSA (Σ : Alphabet) where

record FSA (S : Type) {{_ : DecEq S}} : Type where
  field
    Q  : Set⟨ S ⟩
    -- Σ  : Alphabet
    δ  : S → Token → Maybe S
    Q₀ : ∃ (_∈′ Q)
    -- q₀ : S
    -- q₀∈
    F  : ∃ (_⊆′ Q)

  q₀ = proj₁ Q₀
  fs = proj₁ F

  Δ : S → Word → Maybe (List⁺ S)
  Δ s = go s
    where
      go : S → Word → Maybe (List⁺ S)
      go s ε       = just (s ∷ [])
      go s (t ∷ w) with δ s t
      ... | nothing = nothing
      ... | just s′ = s ∷⁺_ <$> go s′ w

  δ̂ : Word → Maybe S
  δ̂ = (L.NE.head <$>_) ∘ Δ q₀

  isFinal : S → Type
  isFinal = _∈′ fs

open FSA public

-- Example FSA
-- _ : FSA 0|1
-- _ = ?

∁ : ∀ {S} {{_ : DecEq S}} → FSA S → FSA S
∁ record {Q = Q; δ = δ; Q₀ = Q₀; F = (F , F⊆)} =
  record {Q = Q; δ = δ; Q₀ = Q₀; F = (Q ─ F , ∈-─ {xs = Q} {ys = F})}

{-
data Accept : FSA S → Word → Type where
  [δ] : ∀ {w s fsa} → δ̂ fsa w ≡ just s → s ∈′ fs fsa → Accept fsa w
-}


instance
  L-FSA : ∀ {S} {{_ : DecEq S}} → Language (FSA S)
  L-FSA .accept fsa w = ∃ λ s → (δ̂ fsa w ≡ just s) × (isFinal fsa s)

-- To/from Regex
open import Regular Σ

-- Regex properties
⋃-intro : ∀ {w rs r} → r ∈ rs → accept r w → accept (⋃ rs) w
⋃-intro = {!!}

⋃-elim : ∀ {w rs} → accept (⋃ rs) w → ∃ λ r → (r ∈ rs) × (accept r w)
⋃-elim = {!!}

DFA⇒Regex : ∀ {S} {{_ : DecEq S}} → (fsa : FSA S) → Σ[ r ∈ Regex ] (fsa ~ r)
-- fsa → ∃ r. fsa ~ r
DFA⇒Regex {S = S} fsa@(record { Q = ⟨ Q ⟩∶- _ ; δ = δ ; Q₀ = Q₀ , _ ; F = ⟨ F ⟩∶- _ , _ }) =
  r , fsa~r
  where
    -- R _ i j ~ (fsa // i↝j)
    -- R _ i j ~ δ̂
    R : List S → S → S → Regex
    -- Rᵢⱼ⁰
    -- ^ k = 0 (all states > 1)
    R [] i j =
      let αs  = filter (λ α → δ i α ≟ just j) (list Σ)
          Rᵢⱼ = ⋃ mapWith∈ αs (I _ ∘ proj₁ ∘ ∈-filter⁻ _)
      in (if i == j then `ε else `∅) `∪ Rᵢⱼ
    -- Rᵢⱼᵏ = Rᵢⱼᵏ⁻¹ ∪ (Rᵢₖᵏ⁻¹ ∙ Rₖₖᵏ⁻¹ ⋆ ∙ Rₖⱼᵏ⁻¹)
    -- ^ (reverse Q ‼ k:ℕ) = k:S
    R (k ∷ q) i j =
      R q i j `∪ (R q i k ∙ R q k k ⋆ ∙ R q k j)

    R′ : (Q : List S) → (i : S) → (j : S)
       → Σ[ r ∈ Regex ]
           (accept r ⇔ (M.Any.Any ((_⊆ Q) ∘ L.NE.toList) ∘ Δ fsa i))
    R′ = {!!}

    R-δ̂ : ∀ {w f} → f ∈ F → accept fsa w → accept (R Q Q₀ f) w
    R-δ̂ f∈ w∈ = {!!}

    R-δ̂′ : ∀ {w f} → f ∈ F → accept (R Q Q₀ f) w → accept fsa w
    R-δ̂′ = {!!}

    r : Regex
    r = ⋃ (R Q Q₀ <$> F)
      -- R _ Q₀ f ≈ (δ̂ w ≡ just f)
      -- r ~ fsa ∼ ⋃ (fsa // i↝j)

    fsa~r : fsa ~ r
    fsa~r w = p₁ , p₂
      where
        p₁ : accept fsa w → accept r w
        p₁ w∈@(_ , _ , f∈) = ⋃-intro (∈-map⁺ (R Q Q₀) f∈) (R-δ̂ f∈ w∈)

        p₂ : accept r w → accept fsa w
        p₂ w∈rs = let r , r∈ , w∈r = ⋃-elim w∈rs
                      f , f∈ , r≡  = ∈-map⁻ (R Q Q₀) r∈
                  in  R-δ̂′ {f = f} f∈ (subst (flip accept w) r≡ w∈r)

-- _ : proj₁ (DFA⇒Regex fsa)


-- DFA⇒Regex′ : ∀ {S} {{_ : DecEq S}} → (fsa : FSA S) → (fsa ~ DFA⇒Regex fsa)
-- DFA⇒Regex′ fsa = {!!}


-- Regex⇒DFA : Regex → FSA
{-
  ⋃ concatMap (λ f → map (R (q₀ , f)) (enumerate q)) (list fs)
  -- T0D0: find out a recursion principle on lists along with their (relative) indices
  where
    R : ∀ {q = q} → S × S → Index q × S → Regex
    R {q = []} =
      let αs  = filter (λ α → δ i α ≟ just j) (list Σ)
          Rᵢⱼ = ⋃ mapWith∈ αs (I _ ∘ proj₁ ∘ ∈-filter⁻ _)
      in if i == j then
        `ε ∪ Rᵢⱼ
      else
        Rᵢⱼ
    R {q = sₖ ∷ ss} (i , j) (k , sₖ) = {!!}
    R {q = x ∷ x₁ ∷ q} (i , j) (k , sₖ) = {!k!}
-}

{-
    R : ∀ {q} → Index q × S → S → S → Regex
    -- ** base
    R (fzero , _) i j =
      let αs  = filter (λ α → δ i α ≟ just j) (list Σ)
          Rᵢⱼ = ⋃ mapWith∈ αs (I _ ∘ proj₁ ∘ ∈-filter⁻ _)
      in if i == j then
        `ε ∪ Rᵢⱼ
      else
        Rᵢⱼ
    -- ** step
    R {q = .sₖ ∷ q} (fsuc k , sₖ) i j =
      let Rᵢⱼᵏ⁻¹ = R (inject₁ k) i j
          Rᵢₖᵏ⁻¹ = R (inject₁ k) i sₖ
          Rₖₖᵏ⁻¹ = R (inject₁ k) sₖ sₖ
          Rₖⱼᵏ⁻¹ = R (inject₁ k) sₖ j
      in Rᵢⱼᵏ⁻¹ ∪ (Rᵢₖᵏ⁻¹ ∙ Rₖₖᵏ⁻¹ ⋆ ∙ Rₖⱼᵏ⁻¹)
-}

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
