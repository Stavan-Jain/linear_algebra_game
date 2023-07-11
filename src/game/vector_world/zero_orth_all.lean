import vectors.tuple -- hide
import vectors.orthogonal --hide
import data.real.basic
import game.vector_world.triangle_ineq --hide

namespace tuple -- hide

/- 
# Vector world

## Level 22: `Zero orthogonal to all vectors` 

-/

/- Lemma
**0** is orthogonal to all vectors. 
-/

lemma zero_orth_all: ∀ {n : ℕ} (x: ℝ ^ n)
,  orthogonal 0 x   :=
begin
  intros n x,
  induction n with n hn,
  { cases x,
    simp, },
  { cases x with n head tail,
    simp,
    exact hn tail, },
end

end tuple
