import game.norm_orth_world.zero_orth_all

namespace tuple -- hide

/- 
# Norm Orth World

Background:
The parallelogram equality for R² states that the sum of the squares of the diagonals of a parallelogram is equal to twice the sum of the squares of it's adjacent sides. 

Strategy:
As we have seen before, it may be helpful to use the fact that ||x||² can be written as x ⬝ x. 

## Level 4: `Parallelogram equality` 

-/

/- Lemma

-/

lemma parallelogram_eq : ∀ {n : ℕ} (u v : ℝ ^ n), 
(norm_sq (u + v) : ℝ) + ↑(norm_sq (u - v)) = 2 * (↑(norm_sq u) + ↑(norm_sq v)) :=
begin
  intros n u v,
  rw add_norm_square,
  rw sub_norm_square,
  linarith,
end

end tuple
