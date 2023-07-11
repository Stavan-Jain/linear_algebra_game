import vectors.tuple -- hide
import data.real.basic
import game.vector_world.dot_pos_def_1 
namespace tuple -- hide

/- 

Let's come back to thinking about what the dot product describes. It gives us an idea for how much one vector aligns with another. 
The amount that a vector aligns with itself can only be zero if it itself is the zero vector. 
# Vector world

We're going to prove that if dot product of a vector with itself is 0 then it must be the zero vector. 

## Level 5: `dot product is postive definite part 2 ` 

-/

/- Lemma
x ⬝ x = 0 ↔ x = tuple.zero
-/
lemma dot_pos_def_2 : ∀ {n : ℕ} (x : ℝ ^ n),  x ⬝ x = 0 ↔ x = 0 :=
begin 
  intros n x, 
  induction n with d hd,
  { cases x, 
    simp, },
  { cases x with _ head tail, 
    split, 
    { simp,
      intro h,
      have tlt_zero : tail ⬝ tail ≤ 0, 
      { have := mul_self_nonneg head, 
        have : tail ⬝ tail  = - (head * head), 
        { linarith, }, 
        linarith, }, 
      have tgt_zero := dot_pos_def_1 tail,
      have t_eq_zero : tail ⬝ tail = 0, 
      { linarith, }, 
      specialize hd tail,
      rw [t_eq_zero, add_zero] at h,
      rw hd at t_eq_zero,
      split,
      { exact zero_eq_mul_self.mp (eq.symm h), },
      { exact t_eq_zero, },
      },
    { intro h,
      simp at *, 
      rw h.1,
      simp,
      rw [hd tail, h.2], },
    },
end

end tuple -- hide
