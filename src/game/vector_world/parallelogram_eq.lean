import vectors.tuple -- hide
import vectors.orthogonal --hide
import data.real.basic
import game.vector_world.cauchy_schwarz --hide

namespace tuple -- hide

/- 
# Vector world

## Level 19: `Parallelogram equality` 

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
