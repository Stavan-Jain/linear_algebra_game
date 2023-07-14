import game.cauchy_schwarz_world.norm_zero_iff --hide

namespace tuple -- hide

/- 
# Cauchy Schwarz world

## Level 4: `Norm is positive if the vector is nonzero` 

-/

/- Lemma
x ≠ 0 → ‖x‖ > 0 ∀x ∈ Rⁿ 
-/

lemma norm_pos: ∀ {n : ℕ} (x : ℝ ^ n)
, x ≠ 0 → ‖x‖ > 0    :=
begin
  intros n x h,
  have norm_nonzero : ‖x‖ ≠ 0,
        { intro norm_zero,
          apply h,
          exact (norm_zero_iff x).mp norm_zero, },
        repeat {rw norm_eq_sqrt_norm_sq}, simp,
        rw lt_iff_le_and_ne,
        split,
        { exact dot_self_nonneg x, },
        { intro dot_zero,
          apply norm_nonzero,
          repeat {rw norm_eq_sqrt_norm_sq}, simp,
          rw ← dot_zero,
          exact real.sqrt_zero, }, 
end

end tuple -- hide