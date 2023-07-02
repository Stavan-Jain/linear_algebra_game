import vectors.subspace 
import game.vector_world.orth_self_unique_zero

namespace vector_spaces
open tuple

--explain that if `refl,` doesnt work then try using `simp,` or `simpa,`
--refl not working here might have to do with the fact that we 
--reach a goal state (0 : ℝ) + (0 : ℝ) = (0 : ℝ).
--since real numbers are complicated and are defined as limits of
--cauchy sequences, it may be hard for refl to deal with them

instance dot_prod {n : ℕ} {a : ℝ ^ n}: a ≠ 0 → subspace (ℝ ^ n) ℝ {v : ℝ ^ n | a ⬝ v = 0} := 
begin
  intro h,
  constructor,
  { intros u h₁ v h₂,
    simp at *,
    rw [dot_dist, h₁, h₂],
    simp, },
  { intros c v h,
    simp at *,
    rw [dot_comm, scalar_through, dot_comm, h],
    ring, },
  { simp,
   rw [dot_comm, zero_dot],},
end

end vector_spaces