import vectors.tuple -- hide
import vectors.lin_maps --hide
import vectors.tuple.tactics --hide
import data.real.basic
import game.vector_world.orth_self_unique_zero --hide
import game.auxiliary_theorems.zero_smul --hide
import game.vector_spaces_world.vector_space --hide
namespace tuple -- hide

/- 

# Linear Transformation world

## Level 1: `T(0) = 0` 

-/

/- Lemma
x ⬝ x = 0 ↔ x = tuple.zero
-/
lemma id_transformation: ∀ {n : ℕ} (T : ℝ ^ n  → ℝ ^ n),
  (∀ (v : ℝ ^ n), (T v) = v) → linear_transformation T :=
begin 
  intros n T h,
  simp,
  intros c d u v,
  repeat {rw h},
end

end tuple -- hide