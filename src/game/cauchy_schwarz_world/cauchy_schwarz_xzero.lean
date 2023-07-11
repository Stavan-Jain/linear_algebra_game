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
      simp [has_norm.norm, tuple.norm, norm_sq], },
    { cases y with n head tail,
      rw zero_dot,
      simp [has_norm.norm, tuple.norm, norm_sq],
      rw (dot_pos_def_2 0).mpr rfl,
      simp, }, 
  
end

end tuple -- hide
