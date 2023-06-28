import vectors.tuple
import vectors.vector_spaces


namespace vector_spaces

class subspace (𝕍 : Type*) (𝔽 : Type*) [field 𝔽] [vector_space 𝕍 𝔽] (𝕊 : set 𝕍) :=
  (closed_add : ∀ (u v ∈ 𝕊), u + v ∈ 𝕊)
  (closed_smul : ∀ (c : 𝔽) (v ∈ 𝕊), c • v ∈ 𝕊)
  (contains_zero : (0 : 𝕍) ∈ 𝕊)

/-
instance : subspace (ℝ ^ 3) ℝ {[[0, 0, 0]]} := begin
  constructor,

end
-/


end vector_spaces