import vectors.tuple
import vectors.vector_spaces
import vectors.tuple.v_space
import vectors.tuple.tactics


namespace vector_spaces
open tuple

class subspace (𝕍 : Type*) (𝔽 : Type*) [field 𝔽] [vector_space 𝕍 𝔽] (𝕊 : set 𝕍) :=
  (closed_add : ∀ (u v ∈ 𝕊), u + v ∈ 𝕊)
  (closed_smul : ∀ (c : 𝔽) (v ∈ 𝕊), c • v ∈ 𝕊)
  (contains_zero : (0 : 𝕍) ∈ 𝕊)

--def zero_set {n : ℕ }: set (ℝ ^ n) := {v : ℝ ^ n | v = 0}
instance {n : ℕ}: subspace (ℝ ^ n) ℝ {v : ℝ ^ n | v = 0} := begin
  constructor,
  { intros u h1 v h2, 
    simp at *, 
    rw [h1, h2],
    simp, }, 
  { intros, 
  simp at *, 
  induction n with n hn,
  { rw empty_vec_eq_nil v, 
    simp, 
    refl, },
  { cases v with _ v₁ vₙ,
    simp at H ⊢,
    split,
    { right,
      exact H.left, },
    { exact hn vₙ H.right, }, },
  }

end



end vector_spaces