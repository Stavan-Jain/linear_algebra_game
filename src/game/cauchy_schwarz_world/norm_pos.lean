import game.cauchy_schwarz_world.norm_zero_iff --hide

namespace tuple -- hide

/- 
# Cauchy Schwarz world

## Level 8: `Norm is positive if the vector is nonzero` 

-/

/- Lemma

-/

lemma norm_pos: ∀ {n : ℕ} (x : ℝ ^ n)
, x ≠ 0 → ‖x‖ > 0    :=
begin
  intros n x h,
  have norm_nonzero : ‖x‖ ≠ 0,
        { intro norm_zero,
          apply h,
          exact (norm_zero_iff x).mp norm_zero, },
        simp [has_norm.norm, tuple.norm, norm_sq],
        rw lt_iff_le_and_ne,
        split,
        { exact dot_pos_def_1 x, },
        { intro dot_zero,
          apply norm_nonzero,
          simp [has_norm.norm, tuple.norm, norm_sq],
          rw ← dot_zero,
          exact real.sqrt_zero, }, 
end

end tuple -- hide