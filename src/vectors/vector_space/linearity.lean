import vectors.vector_space
-- TODO: n-linear maps/forms

namespace vector_space


section maps
  variables {𝕍₁ : Type*} {𝕍₂ : Type*} {𝕍₃ : Type*} (𝔽 : Type*) [field 𝔽]
    [vector_space 𝕍₁ 𝔽] [vector_space 𝕍₂ 𝔽] [vector_space 𝕍₃ 𝔽]

  class linear_map (f : 𝕍₁ → 𝕍₂) :=
    (add_through : ∀ (u v : 𝕍₁), f (u + v) = f u + f v)
    (smul_through : ∀ (v : 𝕍₁) (c : 𝔽), f (c • v) = c • f v)

  class bilinear_map (f : 𝕍₁ → 𝕍₂ → 𝕍₃) :=
    (left_linear : ∀ (v : 𝕍₂), linear_map 𝔽 (λ u, f u v))
    (right_linear : ∀ (v : 𝕍₁), linear_map 𝔽 (f v))
end maps


section forms
  variables {𝕍 : Type*} {𝔽 : Type*} [field 𝔽] [vector_space 𝕍 𝔽]

  class linear_form (f : 𝕍 → 𝔽) extends linear_map 𝔽 f
  class bilinear_form (f : 𝕍 → 𝕍 → 𝔽) extends bilinear_map 𝔽 f
end forms


end vector_space
