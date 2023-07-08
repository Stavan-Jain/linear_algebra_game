import vectors.tuple -- hide
import vectors.lin_maps --hide
import data.real.basic
import game.vector_world.orth_self_unique_zero --hide
import game.auxiliary_theorems.zero_smul --hide
import game.vector_spaces_world.vector_space --hide
import vectors.subspace --hide
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
