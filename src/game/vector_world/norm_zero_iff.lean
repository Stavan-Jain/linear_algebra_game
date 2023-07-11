import vectors.tuple -- hide
import data.real.basic
import game.vector_world.scalar_norm --hide

namespace tuple -- hide

/- 
# Vector world

## Level 15: `Norm is 0 iff zero vector` 

-/

/- Lemma
||x|| = 0 ↔ x = **0**
-/

set_option pp.numeral_types true

lemma norm_zero_iff : ∀ {n : ℕ} (x : ℝ ^ n), ‖x‖ = 0 ↔ x = 0 :=
begin 
  intros n x,
  simp [has_norm.norm, tuple.norm], -- fix later
  split,
  { intro hx,
    rw real.sqrt_eq_zero at hx,
    { exact (dot_pos_def_2 x).mp hx, },
    { exact dot_pos_def_1 x, }, },
  { intro hx,
    induction n with n hn,
    { cases x,
     simp, },
    { rw hx,
      simp,
      exact hn 0 (by refl), }, 
    },
end

end tuple -- hide
