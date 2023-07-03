import vectors.tuple -- hide
import vectors.lin_maps --hide
import data.real.basic
import game.vector_world.orth_self_unique_zero --hide
import game.auxiliary_theorems.zero_smul --hide
namespace tuple -- hide

/- 

# Linear Transformation world

## Level 1: `T(0) = 0` 

-/

/- Lemma
x ⬝ x = 0 ↔ x = tuple.zero
-/
lemma zero_in_nullspace : ∀ {n m : ℕ} (T : ℝ ^ n  → ℝ ^ m),
  linear_transformation T → ∀ (x : ℝ^ n ), (T 0) = 0 :=
begin 
  intros n m T,
  simp, 
  intro h, 
  have h1 := h 0 0 0 0,
  have := smul_zero, 
   
  exact h1, 
end

end tuple -- hide