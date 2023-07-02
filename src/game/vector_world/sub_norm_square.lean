import vectors.tuple -- hide
import data.real.basic
import game.vector_world.sub_eq_add_neg -- hide

namespace tuple -- hide

/- 
# Vector world

## Level 11: `Subtract norm square` 

-/

/- Lemma
||x - y||² = ||x||² - 2 * (x ⬝ y) + ||y||²
-/


lemma sub_norm_square: ∀ {n : ℕ} (x y : ℝ ^ n)
,  ↑(norm_sq (x - y)) = ↑(norm_sq x) - (2 * (x ⬝ y)) + ↑(norm_sq y) :=
begin 
  intros n x y,
  rw sub_eq_add_neg',
  rw add_norm_square,
  rw neg_eq_neg_mul,
  rw dot_comm x ((-1 : ℝ) • y),
  rw scalar_through,
  rw dot_comm y x,
  simp,
  rw scalar_through,
  rw dot_comm y,
  rw scalar_through,
  linarith,
end

end tuple -- hide
