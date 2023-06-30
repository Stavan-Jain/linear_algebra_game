import vectors.tuple
import vectors.vector_spaces
import vectors.tuple.tactics


namespace vector_spaces
open tuple

class subspace (𝕍 : Type*) (𝔽 : Type*) [field 𝔽] [vector_space 𝕍 𝔽] (𝕊 : set 𝕍) :=
  (closed_add : ∀ (u v ∈ 𝕊), u + v ∈ 𝕊)
  (closed_smul : ∀ (c : 𝔽) (v ∈ 𝕊), c • v ∈ 𝕊)
  (contains_zero : (0 : 𝕍) ∈ 𝕊)

--def zero_set {n : ℕ }: set (ℝ ^ n) := {v : ℝ ^ n | v = 0}


end vector_spaces