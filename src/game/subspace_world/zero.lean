import vectors.subspace
import game.vector_world.smul_zero
namespace vector_spaces
open tuple

instance zero {n : ℕ}: subspace (ℝ ^ n) ℝ {v : ℝ ^ n | v = 0} := begin
  constructor,
  { intros u h1 v h2, 
    simp at *, 
    rw [h1, h2],
    simp, }, 
  { intros, 
  simp at *, 
  rw H,
  exact smul_zero c,}, --explain ambiguous overload
  { simp at *, },
end

end vector_spaces