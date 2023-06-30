import vectors.tuple -- hide
import data.real.basic
import game.vector_world.zero_dot --hide

namespace tuple -- hide

/- 
# Vector world

## Level 18: `Boss level: Cauchy-Schwarz` 

-/

/- Lemma
|x · y| ≤ ||x||*||y||
-/

lemma cauchy_schwarz: ∀ {n : ℕ} (x y : ℝ ^ n)
, |x ⬝ y| ≤ ‖x‖ * ‖y‖    :=
begin
  intros n x y,
  by_cases x_zero : x = 0,
  { cases n,
    { cases x, cases y,
      simp [has_norm.norm, tuple.norm, norm_sq], },
    { rw x_zero,
      cases y with n head tail,
      rw zero_dot,
      simp [has_norm.norm, tuple.norm, norm_sq],
      rw (dot_pos_def_2 0).mpr rfl,
      simp, }, },
  { by_cases y_zero : y = 0,
    { cases n,
      { cases x, cases y,
        simp [has_norm.norm, tuple.norm, norm_sq], },
      { rw y_zero,
        cases x with n head tail,
        rw dot_comm,
        rw zero_dot,
        simp [has_norm.norm, tuple.norm, norm_sq],
        rw (dot_pos_def_2 0).mpr rfl,
        simp, }, },

    { have x_norm_pos : ‖x‖ > 0,
      { have norm_nonzero : ‖x‖ ≠ 0,
        { intro norm_zero,
          apply x_zero,
          exact (norm_zero_iff x).mp norm_zero, },
        simp [has_norm.norm, tuple.norm, norm_sq],
        rw lt_iff_le_and_ne,
        split,
        { exact dot_pos_def_1 x, },
        { intro dot_zero,
          apply norm_nonzero,
          simp [has_norm.norm, tuple.norm, norm_sq],
          rw ← dot_zero,
          exact real.sqrt_zero, }, },

      have y_norm_pos : ‖y‖ > 0,
      { have norm_nonzero : ‖y‖ ≠ 0,
        { intro norm_zero,
          apply y_zero,
          exact (norm_zero_iff y).mp norm_zero, },
        simp [has_norm.norm, tuple.norm, norm_sq],
        rw lt_iff_le_and_ne,
        split,
        { exact dot_pos_def_1 y, },
        { intro dot_zero,
          apply norm_nonzero,
          simp [has_norm.norm, tuple.norm, norm_sq],
          rw ← dot_zero,
          exact real.sqrt_zero, }, },

      have unit_dot_le_1 : |(‖x‖⁻¹ • x) ⬝ (‖y‖⁻¹ • y)| ≤ 1,
      { apply cauchy_schwarz_unit,
        { have mul_inv_unit := div_norm_unit x x_zero,
          simp [has_norm.norm, tuple.norm] at mul_inv_unit ⊢,
          assumption, },
        { have mul_inv_unit := div_norm_unit y y_zero,
          simp [has_norm.norm, tuple.norm] at mul_inv_unit ⊢,
          assumption, }, },

      have h : ‖x‖⁻¹ * ‖y‖⁻¹ * |x ⬝ y| ≤ 1 := by rwa
        [ ← abs_eq_self.mpr (le_of_lt (inv_pos.mpr x_norm_pos))
        , ← abs_eq_self.mpr (le_of_lt (inv_pos.mpr y_norm_pos))
        , ← abs_mul
        , ← abs_mul
        , dot_comm
        , mul_assoc
        , ← scalar_through
        , dot_comm
        , ← scalar_through
        ],

      rw [ ← (one_mul ‖x‖)
         , mul_assoc
         , ← div_le_iff (real.mul_pos x_norm_pos y_norm_pos)
         , div_eq_inv_mul
         ],
      simp,
      linarith, }, },
end

end tuple -- hide
