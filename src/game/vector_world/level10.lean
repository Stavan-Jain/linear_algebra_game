import vectors.tuple -- hide
import data.real.basic
import game.vector_world.level9-- hide 


namespace tuple -- hide

/- 
# Vector world

## Level 10: `Cauchy-Schwarz Inequality for unit vectors` 

-/

/- Lemma
|x · y| ≤ 1 if x and y are unit vectors.
-/

lemma cauchy_schwarz_unit: ∀ {n : ℕ} (x y : ℝ ^ n)
, (norm_sq x) = 1 → (norm_sq y) = 1 → | x ⬝ y| ≤ 1 :=
begin 
  intros n x y x_unit y_unit, 
  have i := add_norm_square x y, 
  have j := sub_norm_square x y, 
  rw x_unit at i, 
  rw y_unit at i, 
  simp at i, 
  have j1: 1 + 2 * x ⬝ y + 1 = 2* (1 + x ⬝ y), 
  {
    linarith, 
  }, 
  rw j1 at i, 
  clear j1 , 
  rw x_unit at j, 
  rw y_unit at j,
  simp at j,
  have j1: 1 - 2 * x ⬝ y + 1 = 2* (1 - x ⬝ y), 
  {
    linarith, 
  }, 
  rw j1 at j, 
  clear j1 ,
  refine abs_le.mpr _, 
  split, 
  {
    have : (x+ y).norm_sq ≥ 0, 
    {
      simp, 
    }, 
    have j : 2 * (1 + x ⬝ y) ≥0 , 
    {
      exact eq.trans_ge i this, 
    }, 
    linarith, 
  }, 
  {
    have : (x- y).norm_sq ≥ 0, 
    {
      simp, 
    }, 
    have j : 2 * (1 - x ⬝ y) ≥0 , 
    {
      exact eq.trans_ge j this, 
    }, 
    linarith, 
  }
end

end tuple -- hide
