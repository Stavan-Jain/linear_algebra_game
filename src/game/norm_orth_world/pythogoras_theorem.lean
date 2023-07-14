import game.norm_orth_world.parallelogram_eq

namespace tuple -- hide

/- 
# Norm Orth World

Background:
The Pythagoras theorem tells us that in a right angled triangle the sum of the sqaures of the perpendicular and the base gives the square
of the hypotenuse. Let us see how to prove the Pythagoras theorem formally in Lean. 

Strategy:
Remember, the "split" tactic allows you to break apart an iff statement into two parts. 

As before, it may be helpful to rewrite ||x||² as x ⬝ x. 

Hint:
1. "perp_ab" introduces a ⟂ b
2. "repeat" allows you to apply a command over and over again. See if you can apply repeat {rw dot_dist} at all
3. You can apply simp to a specific hypothesis by doing "simp at h"

## Level 5: `Pythogoras Theorem` 

-/

/- Lemma
x ⟂ y ↔ ||x+y||² = ||x||² + ||y||²  
-/

lemma pythogaras_theorem : ∀ {n : ℕ} (x y : ℝ ^ n),  
x ⟂ y ↔ ‖x + y‖² = ‖x‖² + ‖y‖² :=
begin 
  intros n x y, 
  split, 
  { intro perp_xy,
    simp,
    rw [dot_dist, dot_comm, dot_comm (x + y)], 
    repeat {rw dot_dist},
    rw dot_comm y,
    simp at perp_xy,
    rw perp_xy,
    simp, },
  { intro h,
    simp at *,
    rw [dot_dist, dot_comm, dot_comm (x + y)] at h,
    repeat {rw dot_dist at h},
    rw dot_comm y at h,
    linarith, },
end


end tuple
