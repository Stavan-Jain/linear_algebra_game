import vectors.tuple -- hide
import data.real.basic
import game.vector_world.level16 --hide

namespace tuple -- hide

/- 
# Vector world

## Level 17: `Triangle Inequality` 

-/

/- Lemma
||x + y|| ≤ ||x|| + ||y||
-/

lemma triangle_ineq: ∀ {n : ℕ} (x: tuple n) (y : tuple n) 
, (x + y).norm ≤ x.norm + y.norm    :=
begin 
  sorry, 
end

end tuple