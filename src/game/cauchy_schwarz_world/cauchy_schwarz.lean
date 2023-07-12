import game.cauchy_schwarz_world.cauchy_schwarz_yzero --hide

namespace tuple -- hide

/- 
# Cauchy Schwarz world

The Cauchy Schwarz inequality is one of the most important concepts you'll learn in an 
introductory linear algebra course. In class you may prove this using the formulas for the dot product and the bounds of the cosine function. 
Here we'll be approaching it differently. 

Strategy:
As in other proofs it may be best to begin by considering the cases when either or both x and y are equal to zero.
Remember, cauchy_schwarz_unit may be helpful here.
modus ponens 
modus ponens reverse -- implication

More info:
All though we’re expressing the cauchy schwarz inequality in terms of the dot product, it actually has to 
do with the inner product (which we will cover more extensively later.) Essentially, the inner product is a 
way to multiply vectors together to get a scalar, within a vector space. The dot product is thus, 
a type of inner product. In a real number space, the inner product is simply multiplication. In a complex vector space, 
the inner product is called the hermitian inner product.

## Level 11: `Boss level: Cauchy-Schwarz` 

-/

/- Lemma
|x · y| ≤ ||x||*||y||

-/

lemma cauchy_schwarz: ∀ {n : ℕ} (x y : ℝ ^ n), |x ⬝ y| ≤ ‖x‖ * ‖y‖ :=
begin
  intros n x y,
  by_cases x_zero : x = 0,
  { rw x_zero, 
    exact cauchy_schwarz_xzero y,  },
  { by_cases y_zero : y = 0,
    { rw y_zero, 
    exact cauchy_schwarz_yzero x,},
    have x_norm_pos := norm_pos x x_zero, 
    have y_norm_pos := norm_pos y y_zero,   
    { have unit_dot_le_1 : |(‖x‖⁻¹ • x) ⬝ (‖y‖⁻¹ • y)| ≤ 1,
      { apply cauchy_schwarz_unit,
        { have mul_inv_unit := div_norm_unit x x_zero,
          repeat {rw norm_eq_sqrt_norm_sq x at mul_inv_unit}, 
          simp at mul_inv_unit,
          repeat {rw norm_eq_sqrt_norm_sq at mul_inv_unit ⊢}, 
          simp at *,
          assumption, },
        { have mul_inv_unit := div_norm_unit y y_zero,
          repeat {rw norm_eq_sqrt_norm_sq y at mul_inv_unit}, 
          simp at mul_inv_unit,
          repeat {rw norm_eq_sqrt_norm_sq at mul_inv_unit ⊢}, 
          simp at *,          
          assumption, }, 
        },

      have h : ‖x‖⁻¹ * ‖y‖⁻¹ * |x ⬝ y| ≤ 1 := by rwa
        [ ← abs_eq_self.mpr (le_of_lt (inv_pos.mpr x_norm_pos))
        , ← abs_eq_self.mpr (le_of_lt (inv_pos.mpr y_norm_pos))
        , ← abs_mul
        , ← abs_mul
        , dot_comm
        , mul_assoc
        , ← scalar_through
        , dot_comm
        , ← scalar_through
        ],

      rw [ ← (one_mul ‖x‖)
         , mul_assoc
         , ← div_le_iff (real.mul_pos x_norm_pos y_norm_pos)
         , div_eq_inv_mul
         ],
      simp,
      linarith, 
      },
    },
end

end tuple -- hide
