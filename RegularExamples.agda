module RegularExamples where

open import Language

module BinaryExample where

  Σ : Alphabet
  Σ = fromList ⟦ '0' , '1' ⟧

  open import Regular Σ

  G⁰ : Regex
  G⁰ = I '0' (here refl)

  G¹ : Regex
  G¹ = I '1' (there (here refl))

  -- (0 | 1((01)⋆0)⋆1)⋆ : binary numbers that are multiples of 3
  Bin3 : Regex
  Bin3 = ( G⁰
         ∪ (G¹ ∙ ((((G⁰ ∙ G¹) ⋆) ∙ G⁰) ⋆) ∙ G¹)
         ) ⋆

  _ : accept Bin3 ⟦ '0' , '0' , '1' , '1' , '0' ⟧
  _ = -- 00110 ∈ G⋆
      inj₂
      -- 00110 ∈ G⁺
      ⟦ # 0 ⇒ˡ -- 0 ∈ G
               inj₁ refl
            ⇒ʳ -- 0110 ∈ G⋆
               inj₂
               -- 0110 ∈ G⁺
               ⟦ # 0 ⇒ˡ -- 0 ∈ G
                        inj₁ refl
                     ⇒ʳ -- 110 ∈ G⋆
                        inj₂
                        -- 110 ∈ G⁺
                        ⟦ # 1 ⇒ˡ -- 11 ∈ G
                                 inj₂ ⟦ # 1 ⇒ˡ -- 1 ∈ G¹
                                               refl
                                            ⇒ʳ -- 1 ∈ (⋯)⋆1
                                               ⟦ # 0 ⇒ˡ -- ε ∈ (⋯)⋆
                                                        inj₁ refl
                                                     ⇒ʳ -- 1 ∈ G¹
                                                        refl ⟧
                                      ⟧
                              ⇒ʳ -- 0 ∈ G⋆
                                 inj₂
                                 -- 0 ∈ G⁺
                                 ⟦ # 0 ⇒ˡ -- 0 ∈ G
                                          inj₁ refl
                                       ⇒ʳ -- ε ∈ G⋆
                                          inj₁ refl
                                 ⟧

                        ⟧
               ⟧
      ⟧
