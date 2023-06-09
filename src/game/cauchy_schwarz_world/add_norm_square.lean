import game.cauchy_schwarz_world.div_norm_unit--hide
import game.auxiliary_theorems.dist_dot --hide
namespace tuple -- hide

/- 
# Cauchy Schwarz world

||x + y||² = ||x||² + 2 * (x ⬝ y) + ||y||²

Background: 

Here we want to prove that ||x + y||² = ||x||² + 2 * (x ⬝ y) + ||y||².

Let us recall that ||x||² can be written as x ⬝ x, and that we know that the dot product is distributive. 

Good luck! 

Strategy:

Let's first get introduced to a tactic called nth_rewrite n rules. It applies the rw tactic 
to the nth possible rule. For instance, nth_rewrite 2 add_comm would apply add_comm to the third possible instance 
where it could be applied. (This is because counting begins from 0.) 

## Level 6: `Add norm square` 

-/

/- Lemma
(x+y)² = x² + 2x⬝y + y² ∀x, y ∈ Rⁿ 
-/

lemma add_norm_square : ∀ {n : ℕ} (x y : ℝ ^ n), 
↑‖x + y‖² = ↑‖x‖² + (2 * (x ⬝ y)) + ↑‖y‖² :=
begin 
  intros n x y, 
  simp,  
  rw [dot_dist, dot_comm, dot_dist],
  rw dist_dot,
  linarith,  
end

end tuple -- hide
