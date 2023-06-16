import vectors.tuple -- hide
import data.real.basic
import game.vector_world.level7-- hide 
import game.vector_world.level3-- hide
import game.vector_world.level4 --hide
import game.vector_world.level8 --hide
import game.vector_world.level12 --hide

namespace tuple -- hide

/- 
# Vector world

## Level 13: `Norm is 0 iff zero vector` 

-/

/- Lemma
||x|| = 0 ↔ x = **0**
-/


#check abs_eq_self
#check scalar_norm
#check inv_mul_cancel
#check real.sqrt_eq_zero
lemma norm_zero_iff: ∀ {n : ℕ} (x: tuple n)
, ↑(x.norm) = (0:ℝ) ↔ x = tuple.zero   :=
begin 
  intros n x, 
  split, 
  {
     dsimp [tuple.norm, norm_sq, dot_product], 
     simp,
     have dot_pos_def: ∀{j :ℕ} (y :tuple j), y ⬝ y = 0 →  y = tuple.zero, {
      intro j, 
      induction j with d hd, 
      intro y, 
      cases y, 
      dsimp [tuple.zero],intro sdvdvs,  refl, 
      intro y, 
      cases y, 
      dsimp [dot_product], 
      intro q, 
      have y_head_nonzero : y_head * y_head ≥ 0 , 
      {
        exact mul_self_nonneg y_head, 
      }, 
      have y_tail_geq : y_tail ⬝ y_tail ≥ 0, 
      {
        exact dot_pos_def_1 y_tail, 
      }, 
      have y_tail_zero : y_tail ⬝ y_tail = 0, 
      {
        linarith [q, y_tail_geq], 
      }, 
      dsimp [tuple.zero], 
      simp, 
      split, 
      {
         rw y_tail_zero at q, simp at q, 
         assumption, 
      }, 
      {
        exact hd y_tail y_tail_zero, 
      }, 
     }, 
     intro h, 
     have k := dot_pos_def_1 x, 
     have r :=  (real.sqrt_eq_zero (dot_pos_def_1 x)).mp h, 
     exact dot_pos_def x r, 
  }, 
  {
    induction n with n ih generalizing x, 
    {
      intro zero, 
      cases x, 
      simp, 
      dsimp [tuple.norm, norm_sq, dot_product], 
      simp,
    }, 
    cases x, 
    intro zero, 
    dsimp [tuple.norm, norm_sq, dot_product], simp, 
    dsimp [tuple.zero] at zero, 
    simp at zero, 
    cases zero with l r, 
    rw l, rw r, simp, 
    have k := ih x_tail r,
    dsimp [tuple.norm] at k, simp at k,
    dsimp [norm_sq] at k,
    simp at k, 
    rw ← r, rw k, 
    simp,  
  }
end

end tuple -- hide