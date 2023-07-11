import vectors.subspace
import game.norm_orth_world.triangle_ineq
import game.vector_spaces_world.vector_space
namespace vector_spaces
open tuple

instance zero {n : ℕ} : subspace (ℝ ^ n) ℝ {v : ℝ ^ n | v = 0} := 
begin
  split,

  { intros u h1 v h2, 
    simp at *, 
    rw [h1, h2],
    simp, },

  { intros, 
    simp at *, 
    rw [H, smul_zero'], }, 
    
  { simp at *, },
end

end vector_spaces