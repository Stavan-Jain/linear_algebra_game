import vectors.tuple -- hide
import data.real.basic
import game.vector_world.dot_dist-- hide 
namespace tuple -- hide

/- 
# Vector world

## Level 8: `Add norm square` 

-/

/- Lemma
||x + y||² = ||x||² + 2 * (x ⬝ y) + ||y||²
-/

lemma add_norm_square : ∀ {n : ℕ} (x y : ℝ ^ n), 
↑(norm_sq (x + y)) = ↑(norm_sq x) + (2 * (x ⬝ y)) + ↑(norm_sq y) :=
begin 
  intros n x y, 
  simp,  
  rw [dot_dist, dot_comm, dot_dist],
  nth_rewrite 2 dot_comm, 
  rw dot_dist, 
  nth_rewrite 2 dot_comm,
  linarith,  
end

end tuple -- hide
