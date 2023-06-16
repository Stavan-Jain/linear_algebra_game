import vectors.tuple -- hide
import data.real.basic
import game.vector_world.level7-- hide 
import game.vector_world.level3-- hide
import game.vector_world.level8 --hide
import game.vector_world.level10 --hide
import game.vector_world.level12 --hide
import game.vector_world.level13 --hide
import game.vector_world.level14 -- hide
import game.vector_world.level15 --hide

namespace tuple -- hide

/- 
# Vector world

## Level 15: `Boss level: Cauchy-Schwarz` 

-/

/- Lemma
|x · y| ≤ ||x||*||y||
-/


#check abs_eq_self
#check scalar_norm
#check inv_mul_cancel
lemma cauchy_schwarz: ∀ {n : ℕ} (x: tuple n) (y : tuple n) 
, | x ⬝ y| ≤ x.norm *y.norm    :=
begin 
  intros n x y, 
  by_cases (x= tuple.zero),
  {cases x, 
    {dsimp [tuple.norm, norm_sq, dot_product],
    simp, },
    {
      rw h, 
      dsimp [dot_product],
      cases y, 
      dsimp [tuple.zero, tuple.norm, norm_sq, dot_product],
      simp,  
      repeat {rw zero_dot},
      simp,  
    },
  }, 
  {
    by_cases h2 : (y = tuple.zero) , 
    {
      rw h2, 
      dsimp [tuple.zero, tuple.norm, norm_sq, dot_product],
      simp,  
      repeat {rw zero_dot},
      simp,
      rw dot_comm, 
      exact zero_dot x, 
    } , 
    {
      have non_zero : x.norm > 0 ∧ y.norm > 0, 
      sorry {
        split, 
        {
          have h5: ↑x.norm ≠ (0:ℝ)  , 
          {
            by_contra h3, 
            have h4:= (norm_zero_iff x).mp h3, 
            exact h h4,
          }, 
          simp at h5, 
          have h6 := dot_pos_def_1 x,
          exact zero_lt_iff.mpr h5,
        }, 
        {
            have h5: ↑y.norm ≠ (0:ℝ)  , 
          {
            by_contra h3, 
            have h4:= (norm_zero_iff y).mp h3, 
            exact h2 h4,
          }, 
          simp at h5, 
          have h6 := dot_pos_def_1 y,
          exact zero_lt_iff.mpr h5,
        }, 
      }, 
      cases non_zero with x_nonzero y_nonzero, 
      have h3 : |((1  /  x.norm)** x) ⬝ ((1 / y.norm)** y)| ≤ 1, 
      {
        have h4 : x ≠ tuple.zero, 
        {
          exact h
        },
        have h5 : y ≠ tuple.zero, 
        {
          exact h2
        },
        have h6:= div_norm_unit x h4, 
        have h7:= div_norm_unit y h5,   
        have h9 : (1 / ↑(x.norm) ** x).norm_sq = 1, 
        {
          dsimp [tuple.norm] at h6,  simp at h6,
          dsimp [tuple.norm], simp, assumption,  
        }, 
        have h10 : (1 / ↑(y.norm) ** y).norm_sq = 1,
        {
          dsimp [tuple.norm] at h7,  simp at h7,
          dsimp [tuple.norm], simp, assumption,  
        }, 
        have h8:=  cauchy_schwarz_unit (1 / x.norm ** x) ( 1 / y.norm ** y) h9 h10,
        exact h8, 
      }, 
      have h4 : ((1 / x.norm) : ℝ)  * |x ⬝ ((1/y.norm)** y)| ≤ 1, 
      {
        sorry, 
      }, 


    }
  }, 



end

end tuple -- hide