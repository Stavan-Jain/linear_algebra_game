import vectors.tuple -- hide
import data.real.basic
import game.vector_world.level7-- hide 
import game.vector_world.level3-- hide

namespace tuple -- hide

/- 
# Vector world

## Level 8: `Add norm square` 

-/

/- Lemma
||x + y||² = ||x||² + 2 * (x ⬝ y) + ||y||²
-/

lemma add_norm_square: ∀ {n : ℕ} (x: tuple n) (y : tuple n) 
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