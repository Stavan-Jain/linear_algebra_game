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
  simp, 
  intros n m T h,
  specialize h 0 0 0 0,
  repeat {rw smul_zero' at h,  rw zero_smul' at h}, 
  simp at h, 
  exact h, 
end

end vector_spaces -- hide
