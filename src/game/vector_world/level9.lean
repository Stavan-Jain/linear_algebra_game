import vectors.tuple -- hide
import data.real.basic
import game.vector_world.level8 --hide

namespace tuple -- hide

/- 
# Vector world

## Level 9: `Add norm square` 

-/

/- Lemma
||x + y||² = ||x||² + 2 * (x ⬝ y) + ||y||²
-/


lemma sub_norm_square: ∀ {n : ℕ} (x: tuple n) (y : tuple n) 
,  ↑(norm_sq (x - y)) = ↑(norm_sq x) - (2 * (x ⬝ y)) + ↑(norm_sq y) :=
begin 
  sorry,  
end

end tuple -- hide