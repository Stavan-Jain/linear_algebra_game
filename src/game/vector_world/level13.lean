import vectors.tuple -- hide
import data.real.basic
import game.vector_world.level7-- hide 
import game.vector_world.level3-- hide
import game.vector_world.level8 --hide

namespace tuple -- hide

/- 
# Vector world

## Level 13: `Unit vector stuff` 

-/

/- Lemma
||x + y||² = ||x||² + 2 * (x ⬝ y) + ||y||²
-/


lemma div_norm_unit: ∀ {n : ℕ} (x: tuple n)
, x ≠ tuple.zero →  norm_sq ((1 / norm x) ** x) = 1  :=
begin 
  intros n x xneq, 
  simp [norm_sq, norm],
  dsimp [tuple.norm], 
  simp,   
  

end

end tuple -- hide