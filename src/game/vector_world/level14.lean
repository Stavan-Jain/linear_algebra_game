import vectors.tuple -- hide
import data.real.basic
import game.vector_world.level13 --hide

namespace tuple -- hide

/- 
# Vector world

## Level 14: `Unit vector stuff` 

-/

/- Lemma
||(1 / ||x|| ) *x || = 1
-/

lemma div_norm_unit: ∀ {n : ℕ} (x: ℝ ^ n)
, x ≠ 0 → ‖(1 / ‖x‖) ** x‖ = (1:ℝ) :=
begin 
  intros n x xneq,
  rw ← scalar_norm (1 / ‖x‖) x,
  have j : 0 ≤ (1 / ‖x‖ : ℝ),
  { simp [has_norm.norm, tuple.norm, norm_sq],
    exact real.sqrt_nonneg _, },
  rw abs_eq_self.mpr j,
  simp [has_norm.norm, tuple.norm, norm_sq],
  apply inv_mul_cancel,
  rw real.sqrt_ne_zero,
  { intro x_dot_0,
    apply xneq,
    rw ← dot_pos_def_2,
    exact x_dot_0, },
  { exact dot_pos_def_1 x, },
end

end tuple -- hide

