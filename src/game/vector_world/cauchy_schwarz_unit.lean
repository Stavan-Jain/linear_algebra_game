import vectors.tuple -- hide
import data.real.basic
import game.vector_world.sub_norm_square -- hide 


namespace tuple -- hide

/- 
# Vector world

## Level 12: `Cauchy-Schwarz Inequality for unit vectors` 

-/

/- Lemma

|x · y| ≤ 1 if x and y are unit vectors.

In class you can prove this using the formula for the magnitude of the 
dot product and the bounds of the cosine function. 

Here we'll be approaching it differently. 

Hint: 
We will be using the fact that |x · y|² is ≥ 1. 
Applying add_norm_square we see that that |x · y|²= ||x||² + 2 * (x ⬝ y) + ||y||² ≥ 1 

Good luck!

-/

lemma cauchy_schwarz_unit: ∀ {n : ℕ} (x: tuple n) (y : tuple n) 
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