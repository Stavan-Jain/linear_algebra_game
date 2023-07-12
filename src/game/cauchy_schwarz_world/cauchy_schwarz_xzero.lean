import game.cauchy_schwarz_world.norm_pos --hide

namespace tuple -- hide

/- 
# Cauchy Schwarz world

## Level 9: `Cauchy-Schwarz when x = 0` 

The Cauchy Schwarz Inequality when one of the vectors is 0. 
-/

/- Lemma

-/

lemma cauchy_schwarz_xzero: ∀ {n : ℕ} ( y : ℝ ^ n)
, |0 ⬝ y| ≤ ‖(0 : ℝ ^ n) ‖ * ‖y‖    :=
begin
  intros n y,
  cases n,
    { cases y,
      repeat {rw norm_eq_sqrt_norm_sq}, simp,  },
    { cases y with n head tail,
      rw zero_dot,
      repeat {rw norm_eq_sqrt_norm_sq}, simp, 
      rw (dot_self_zero 0).mpr rfl,
      simp, }, 
  
end

end tuple -- hide
