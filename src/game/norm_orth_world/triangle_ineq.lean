import game.norm_orth_world.pythogoras_theorem --hide

namespace tuple -- hide

/- 
# Vector world

Background:
When you're introduced to the triangle inquality in an introductory geometry class it states that 
in a triangle with sides of length a, b, and c the length of any one side a is less than or 
equal to the sum of lenghts of the other two sides b and c, (a being equal to b + c when all 
three sides lie on the same line.) 
The triangle inequality can be extrpolated to Rⁿ to show that for any two vectors x and y 
the magnitude of their sum is less than or equal to the sum of their individual lengths.  
In class, you may prove this case by case, considering the possibility that either or both x, y are 0, x is positive while y is negative (or vice versa),
or they're both either postive or negative. 

Strategy:


## Level 6: `Triangle Inequality` 

-/

/- Lemma
||x + y|| ≤ ||x|| + ||y||


-/

lemma triangle_ineq: ∀ {n : ℕ} (x: ℝ ^ n) (y : ℝ ^ n) 
, ‖x + y‖ ≤ ‖x‖ + ‖y‖ :=
begin 
  intros n x y, 
  have h1:= add_norm_square x y,
  have h2 := cauchy_schwarz x y,
  have h3 : x ⬝ y ≤ |x ⬝ y|, 
  {
    exact le_abs_self (x ⬝ y), 
  },
  have h4 : ((x + y).norm_sq) ≤ ((‖x‖₊ + ‖y‖₊)^2),
  {
    calc ↑((x + y).norm_sq) = ↑(x.norm_sq) + 2 * x ⬝ y + ↑(y.norm_sq) : h1
      ... ≤ ↑(x.norm_sq) + 2 * |x ⬝ y| + ↑(y.norm_sq) : by linarith
      ... ≤ ↑(x.norm_sq) + 2 * ‖x‖ * ‖y‖ + ↑(y.norm_sq) : by { simp, linarith, }
      ... =  ((‖x‖ + ‖y‖)^2) : begin
        rw add_sq,
        have hx_sqrt := real.sq_sqrt(dot_pos_def_1 x),
        have hy_sqrt := real.sq_sqrt(dot_pos_def_1 y),
        simp [norm_eq_sqrt_norm_sq, hx_sqrt, hy_sqrt],
      end
  }, 
  clear h3 h2 h1, 
  repeat { rw norm_eq_sqrt_norm_sq },

  have i := nnreal.sqrt_le_sqrt_iff.mpr h4, 
  rw nnreal.sqrt_sq at i,  
  exact i, 
end

end tuple
