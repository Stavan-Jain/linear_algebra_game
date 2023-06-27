import vectors.tuple -- hide
import vectors.orthogonal --hide
import data.real.basic
import game.vector_world.level8 --hide
import game.vector_world.level9 --hide

namespace tuple -- hide

/- 
# Vector world

## Level 18: `Zero orthogonal` 

-/

/- Lemma
**0** is orthogonal to all vectors. 
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
