import vectors.subspace
import game.vector_world.smul_zero
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
  rw H,
  exact smul_zero c,}, --explain ambiguous overload
  { simp at *, },
end

end vector_spaces