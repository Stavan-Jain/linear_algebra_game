import game.cauchy_schwarz_world.cauchy_schwarz_xzero --hide

namespace tuple -- hide

/- 
# Cauchy Schwarz world

## Level 10: `Cauchy-Schwarz when y = 0` 

The Cauchy Schwarz Inequality when one of the vectors is 0. 
-/

/- Lemma
∀ {n : ℕ} (x : ℝ ^ n), |x ⬝ 0| ≤ ‖x ‖ * ‖0‖ 
-/

lemma cauchy_schwarz_yzero: ∀ {n : ℕ} (x : ℝ ^ n)
, |x ⬝ 0| ≤ ‖x ‖ * ‖(0 : ℝ ^ n)‖    :=
begin
  intros n x,
  cases n,
    { cases x,
      simp [has_norm.norm, tuple.norm, norm_sq], },
    { cases x with n head tail,
      rw dot_zero,
      simp [has_norm.norm, tuple.norm, norm_sq],
      rw (dot_self_zero 0).mpr rfl,
      simp, }, 
end

end tuple -- hide
