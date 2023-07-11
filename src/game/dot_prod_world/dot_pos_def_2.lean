import game.dot_prod_world.dot_pos_def_1 --hide
namespace tuple -- hide

/- 

Let's come back to thinking about what the dot product describes. It gives us an idea for how much one vector aligns with another. 
The amount that a vector aligns with itself can only be zero if it itself is the zero vector. 
# Vector world

We're going to prove that if dot product of a vector with itself is 0 then it must be the zero vector. 

## Level 3: `dot product is postive definite part 2 ` 

-/

/- Lemma
x ⬝ x = 0 ↔ x = tuple.zero
-/
lemma dot_pos_def_2: ∀ {n : ℕ} (x : ℝ ^ n),  x ⬝ x = 0 ↔ x = 0 :=
begin 
  intro n, 
  induction n with d hd,
  { intro x, cases x, dsimp [dot_product], split, 
  intro h, 
   refl, intro h, refl, },
  {
    intro x, cases x , split, 
    dsimp [dot_product], intro h, 
    have tlt_zero :x_tail ⬝ x_tail ≤ 0, 
    {
      have : x_head*x_head ≥ 0, 
      {
        exact mul_self_nonneg x_head
      }, 
      have : x_tail ⬝ x_tail  = - (x_head*x_head) , {
        linarith, 
      } , 
      linarith, 
    }, 
    have tgt_zero := dot_pos_def_1 x_tail,
    have t_eq_zero : x_tail ⬝ x_tail = 0 , {
      linarith, 
    } , 
    {
      simp,
      rw [t_eq_zero, add_zero] at h, 
      split, 
      {
        exact zero_eq_mul_self.mp (eq.symm h), 
      }, 
    exact (hd x_tail).mp t_eq_zero,  
    },
    intro h, 
    dsimp [dot_product], 
    dsimp [tuple.zero] at h, 
    simp at *,  
    cases h with head_eq_zero tail_dot_eq_zero,
    rw head_eq_zero, simp, 
    exact (hd x_tail).mpr tail_dot_eq_zero, 
  },
end

end tuple -- hide
