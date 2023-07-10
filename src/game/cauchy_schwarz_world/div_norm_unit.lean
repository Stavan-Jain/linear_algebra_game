import vectors.tuple -- hide
import data.real.basic
import game.vector_world.norm_zero_iff --hide

namespace tuple -- hide

/- 
# Vector world

## Level 16: `Div norm unit` 

-/

/- Lemma
||(1 / ||x|| ) *x || = 1
-/

lemma div_norm_unit: ∀ {n : ℕ} (x: ℝ ^ n)
, x ≠ 0 → ‖ ‖x‖⁻¹ • x‖ = 1 :=
begin 
  intros n x xneq,
  rw ← scalar_norm (‖x‖⁻¹) x,
  have j : 0 ≤ (‖x‖⁻¹ : ℝ),
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

