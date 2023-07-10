import game.dot_prod_world.dot_zero
import game.auxiliary_theorems.sub_eq_add_neg --hide
namespace tuple -- hide

/- 
# Cauchy Schwarz world

## Level 1: `Add norm square` 

-/

/- Lemma
||x + y||² = ||x||² + 2 * (x ⬝ y) + ||y||²
-/

lemma add_norm_square: ∀ {n : ℕ} (x y : ℝ ^ n)
,  ↑(norm_sq (x + y)) = ↑(norm_sq x) + (2 * (x ⬝ y)) + ↑(norm_sq y) :=
begin 
  intros n x y, 
  simp,   
  rw dot_dist, 
  rw dot_comm, 
  rw dot_dist, 
  nth_rewrite 2 dot_comm, 
  rw dot_dist, 
  nth_rewrite 2 dot_comm,
  linarith,  
end

end tuple -- hide
