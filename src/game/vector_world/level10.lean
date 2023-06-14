import vectors.tuple -- hide
import data.real.basic
import game.vector_world.level7-- hide 

namespace tuple -- hide

/- 
# Vector world

## Level 10: `Cauchy-Schwarz Inequality for unit vectors` 

-/

/- Lemma
|x · y| ≤ 1 if x and y are unit vectors.-/

lemma cauchy_schwarz_unit: ∀ {n : ℕ} (x: tuple n) (y : tuple n) 
, (norm_sq x) = 1 → (norm_sq y) = 1 → | x ⬝ y| ≤ 1 :=
begin 
  intros n x y x_unit y_unit, 
end

end tuple -- hide