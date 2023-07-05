import vectors.tuple -- hide
import vectors.lin_maps --hide
import data.real.basic
import game.vector_world.orth_self_unique_zero --hide
import game.auxiliary_theorems.zero_smul --hide
import game.vector_spaces_world.vector_space --hide
import vectors.subspace --hide
namespace tuple -- hide

/- 

# Linear Transformation world

## Level 1: `T(0) = 0` 

-/

/- Lemma
x ⬝ x = 0 ↔ x = tuple.zero
-/
lemma zero_in_kernel : ∀ {n m : ℕ} (T : ℝ ^ n  → ℝ ^ m),
  linear_transformation T → (T 0) = 0 :=
begin 
  intros n m T,
  simp, 
  intro h, 
  have h1 := h 0 0 0 0,
  repeat {rw smul_zero' at h1,  rw zero_smul' at h1}, 
  simp at h1, 
  exact h1, 
end

end tuple -- hide