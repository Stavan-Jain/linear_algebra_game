import game.cauchy_schwarz_world.sub_norm_square --hide
namespace tuple -- hide

/- 
# Cauchy Schwarz world

Background:
Here we will be proving the following: |x · y| ≤ 1 if x and y are unit vectors.

In class you can prove this using the formula for the magnitude of the 
dot product and the bounds of the cosine function. 

Here we'll be approaching it differently. 

Strategy: 
We will be using the fact that |x · y|² is ≥ 1. 
Applying add_norm_square we see that that |x · y|²= ||x||² + 2 * (x ⬝ y) + ||y||² ≥ 1 

Good luck!

## Level 12: `Cauchy-Schwarz Inequality for unit vectors` 

-/

/- Lemma
|x · y| ≤ 1 if x and y are unit vectors.

-/

lemma cauchy_schwarz_unit : ∀ {n : ℕ} (x y : ℝ ^ n), 
(norm_sq x) = 1 → (norm_sq y) = 1 → |x ⬝ y| ≤ 1 :=
begin 
  intros n x y x_unit y_unit, 
  have h₁ := add_norm_square x y, 
  have h₂ := sub_norm_square x y, 
  rw x_unit at h₁, 
  rw y_unit at h₁, 
  simp at h₁, 
  have : 1 + 2 * x ⬝ y + 1 = 2 * (1 + x ⬝ y) := by linarith, 
  rw this at h₁, 
  clear this, 
  rw x_unit at h₂, 
  rw y_unit at h₂,
  simp at h₂,
  have : 1 - 2 * x ⬝ y + 1 = 2* (1 - x ⬝ y) := by linarith, 
  rw this at h₂, 
  clear this,
  apply abs_le.mpr,
  split, 
  { have i : (x+ y).norm_sq ≥ 0 := by simp, 
    have j : 2 * (1 + x ⬝ y) ≥0 := by exact eq.trans_ge h₁ i, 
    linarith, }, 
  { have i : (x- y).norm_sq ≥ 0 := by simp, 
    have j : 2 * (1 - x ⬝ y) ≥0 := by exact eq.trans_ge h₂ i,
    linarith, },
end

end tuple -- hide
