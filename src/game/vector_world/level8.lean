import vectors.tuple -- hide
import data.real.basic
namespace tuple -- hide

/- 
# Vector world

## Level 8: `Add norm square` 

-/

/- Lemma
||x + y||² = ||x||² + 2 * (x ⬝ y) + ||y||²
-/

lemma add_norm_square: ∀ {n : ℕ} (x: tuple n) (y : tuple n) 
,  norm_sq (x + y) = norm_sq x + (2 * (x ⬝ y)) + norm_sq y :=
begin 
  sorry, 

end

end tuple -- hide