import game.subspace_world.line

namespace vector_spaces
open tuple

-- why is a ≠ 0? Shouldn't the statement be true even if a = 0?

instance dot_prod {n : ℕ} {a : ℝ ^ n}: a ≠ 0 → subspace (ℝ ^ n) ℝ {v : ℝ ^ n | a ⬝ v = 0} := 
begin
  intro h,
  split,
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