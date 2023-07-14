import game.cauchy_schwarz_world.cauchy_schwarz_xzero --hide

namespace tuple -- hide

/- 
# Cauchy Schwarz world

## Level 10: `Cauchy-Schwarz when y = 0` 

The Cauchy Schwarz Inequality when one of the vectors is 0. 
-/

/- Lemma
|x ⬝ 0| ≤ ‖x‖ * ‖0‖ ∀x ∈ Rⁿ 
-/

lemma cauchy_schwarz_yzero: ∀ {n : ℕ} (x : ℝ ^ n),
 |x ⬝ 0| ≤ ‖x‖ * ‖(0 : ℝ ^ n)‖ :=
begin
  intros n x,
  cases n,
    { cases x,
      repeat {rw norm_eq_sqrt_norm_sq}, simp, },
    { cases x with n head tail,
      rw dot_zero,
      repeat {rw norm_eq_sqrt_norm_sq}, simp,
      rw (dot_self_zero 0).mpr rfl,
      simp, }, 
end

end tuple -- hide
