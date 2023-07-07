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
lemma example_1: ∀ (T : ℝ ^ 2  → ℝ ^ 2),
  (∀ (x y: ℝ ), (T [[x, y]]) = [[ (x + y), y]]) → linear_transformation T :=
begin 
  intros T h,
  simp, 
  intros c d u v,
  cases u with _ u₁ tail,
  cases tail with _ u₂ tail,
  cases tail,
  cases v with _ v₁ tail,
  cases tail with _ v₂ tail,
  cases tail,
  simp,
  repeat {rw h},
  simp,
  ring, 
end

end tuple -- hide