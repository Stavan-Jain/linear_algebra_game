import vectors.subspace
import game.vector_world.orth_self_unique_zero
import game.auxiliary_theorems.zero_smul
import game.vector_spaces_world.vector_space
namespace vector_spaces
open tuple

instance zero {n : ℕ}: subspace (ℝ ^ n) ℝ {v : ℝ ^ n | v = 0} := begin
  constructor,
  { intros u h1 v h2, 
    simp at *, 
    rw [h1, h2],
    simp,
  },

  { intros, 
  simp at *, 
  rw H, rw smul_zero', }, --explain ambiguous overload
  { simp at *, },
end

end vector_spaces