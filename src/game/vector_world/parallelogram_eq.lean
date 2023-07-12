import vectors.tuple -- hide
import vectors.orthogonal --hide
import data.real.basic
import game.vector_world.cauchy_schwarz --hide

namespace tuple -- hide

/- 
# Vector world

Background:
The parallelogram equality for R² states that the sum of the squares of the diagonals of a parallelogram is equal to twice the sum of the squares of it's adjacent sides. 

Strategy:
As we have seen before, it may be helpful to use the fact that ||x||² can be written as x ⬝ x. 


## Level 19: `Parallelogram equality` 

-/

/- Lemma
||u + v||² + ||u - v||² = 2||u||² + 2||v||² 

-/

lemma parallelogram_eq: ∀ {n : ℕ} (u v : ℝ ^ n)
, (norm_sq (u + v) : ℝ) + ↑(norm_sq (u - v)) = 2 * (↑(norm_sq u) + ↑(norm_sq v)) :=
begin
  intros n u v,
  rw add_norm_square,
  rw sub_norm_square,
  linarith,
end

end tuple
