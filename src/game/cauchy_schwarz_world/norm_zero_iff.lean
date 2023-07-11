import game.cauchy_schwarz_world.cauchy_schwarz_unit

namespace tuple -- hide

/- 
# Cauchy Schwarz World

## Level 7: `Norm is 0 iff zero vector` 

-/

/- Lemma
||x|| = 0 ↔ x = **0**

Background: 

Here we'll be proving that the magnitude of a vector is 0 if and only if it is the zero vector. 

Let's think about this in R². Let's say that there is some vector who's magnitude is found to be 0. This can only be true it's length in 0, i.e. it is the zero vector.

Strategy: 

As we've seen repeatedly it might also be helpful in this case to express the magnitude of x as 
the dot product of x with itself. 


-/

set_option pp.numeral_types true

lemma norm_zero_iff : ∀ {n : ℕ} (x : ℝ ^ n), ‖x‖ = 0 ↔ x = 0 :=
begin 
  intros n x,
  repeat {rw norm_eq_sqrt_norm_sq}, simp,
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
