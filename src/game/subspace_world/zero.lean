import vectors.subspace
import game.vector_spaces_world.vector_space

namespace vector_spaces
open tuple
set_option pp.numeral_types true
instance zero {n : ℕ}: subspace (ℝ ^ n) ℝ {v : ℝ ^ n | v = 0} := begin
  constructor,
  { intros u h1 v h2, 
    simp at *, 
    rw [h1, h2],
    simp,
  },

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
  },
simp, 
end

end vector_spaces