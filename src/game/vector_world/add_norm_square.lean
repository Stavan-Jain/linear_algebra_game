import vectors.tuple -- hide
import data.real.basic
import game.vector_world.dot_dist-- hide 
namespace tuple -- hide

/- 
# Vector world

||x + y||² = ||x||² + 2 * (x ⬝ y) + ||y||²

Background: 

Here we want to prove that ||x + y||² = ||x||² + 2 * (x ⬝ y) + ||y||².

Let us recall that ||x||² can be written as x ⬝ x, and that we know that the dot product is distributive. 

Good luck! 

Strategy:

Let's first get introduced to a tactic called nth_rewrite n rules. It applies the rw tactic 
to the nth possible rule. For instance, nth_rewrite 2 add_comm would apply add_comm to the third possible instance 
where it could be applied. (This is because counting begins from 0.) 

## Level 8: `Add norm square` 

-/

/- Lemma


-/

lemma add_norm_square: ∀ {n : ℕ} (x y : ℝ ^ n)
,  ↑(norm_sq (x + y)) = ↑(norm_sq x) + (2 * (x ⬝ y)) + ↑(norm_sq y) :=
begin 
  intros n x y, 
  dsimp [norm_sq],  
  rw dot_dist, 
  rw dot_comm, 
  rw dot_dist, 
  nth_rewrite 2 dot_comm, 
  rw dot_dist, 
  nth_rewrite 2 dot_comm,
  linarith,  
end

end tuple -- hide
