import game.dot_prod_world.dot_self_nonneg --hide
namespace tuple -- hide

/- 
# Dot Product World

Let's come back to thinking about what the dot product describes. It gives us an idea for how much one vector aligns with another. 
The amount that a vector aligns with itself can only be zero if it itself is the zero vector. 

We're going to prove that if dot product of a vector with itself is 0 then it must be the zero vector. 

## Level 3: `dot product is postive definite part 2 ` 

-/

/- Lemma
x ⬝ x = 0 ↔ x = tuple.zero
-/
lemma dot_self_zero : ∀ {n : ℕ} (x : ℝ ^ n),  x ⬝ x = 0 ↔ x = 0 :=
begin 
  intros n x, 
  split,
  { intro h, 
    induction n with d hd,
    { cases x,
      simp, },
    { cases x with n head tail,
      simp at *,
      have : tail ⬝ tail  = - (head * head) := 
        by linarith [mul_self_nonneg head],
      have tlt_zero : tail ⬝ tail ≤ 0 
        := by linarith [mul_self_nonneg head],
      have tgt_zero := dot_self_nonneg tail,
      have t_eq_zero : tail ⬝ tail = 0 := by linarith,
      specialize hd tail,
      rw [t_eq_zero, add_zero] at h,
      split,
      { exact zero_eq_mul_self.mp (eq.symm h), },
      { exact hd t_eq_zero, },
      }, 
    },
    
    { intro h,
      rw [h, zero_dot], },
end

end tuple -- hide
