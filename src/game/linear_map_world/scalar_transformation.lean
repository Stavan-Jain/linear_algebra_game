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
lemma scalar_transformation: ∀ {n : ℕ} (T : ℝ ^ n  → ℝ ^ n) (a : ℝ),
  (∀ (v : ℝ ^ n), (T v) = a • v) → linear_transformation T :=
begin 
  intros n T a h,
  simp,
  intros c d u v,
  repeat {rw h},
  rw scalar_dist_1,
  repeat {rw scalar_assoc},
  ring_nf,
end

end tuple -- hide