import vectors.lin_maps --hide
import game.subspace_world.orth_of_sum_eq_inter_of_orth--hide
open tuple -- hide
namespace vector_spaces --hide

/- 

# Linear Transformation world

## Level 1: `T(0) = 0` 

-/

/- Lemma
x ⬝ x = 0 ↔ x = tuple.zero
-/

lemma zero_in_kernel : ∀ {n m : ℕ} (T : ℝ ^ n → ℝ ^ m),
  linear_transformation T ℝ → (T 0) = 0 :=
begin 
  intros n m T,
  simp, 
  intro h, 
  have h1 := h 0 0 0 0,
  repeat {rw smul_zero' at h1,  rw zero_smul' at h1}, 
  simp at h1, 
  exact h1, 
end

end vector_spaces -- hide
