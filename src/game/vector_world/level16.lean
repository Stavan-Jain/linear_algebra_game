import vectors.tuple -- hide
import data.real.basic
import game.vector_world.level7-- hide 
import game.vector_world.level3-- hide
import game.vector_world.level8 --hide
import game.vector_world.level12 --hide
import game.vector_world.level13 --hide

namespace tuple -- hide

/- 
# Vector world

## Level 15: `Boss level: Cauchy-Schwarz` 

-/

/- Lemma
|x · y| ≤ ||x||*||y||
-/


#check abs_eq_self
#check scalar_norm
#check inv_mul_cancel
lemma div_norm_unit: ∀ {n : ℕ} (x: tuple n) (y : tuple n) 
, | x ⬝ y| ≤ x.norm *y.norm    :=
begin 
  intros n x y, 
  cases x, 
  dsimp [tuple.norm, norm_sq, dot_product],
  simp,  



end

end tuple -- hide