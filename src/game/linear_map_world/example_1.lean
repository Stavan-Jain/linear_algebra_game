import game.linear_map_world.zero_transformation
namespace vector_spaces
open tuple -- hide

/- 

# Linear Transformation world

## Level 5: `Random linear transformation` 

-/

/- Lemma
x ⬝ x = 0 ↔ x = tuple.zero
-/
lemma example_1: ∀ (T : ℝ ^ 2  → ℝ ^ 2),
  (∀ (x y: ℝ ), (T [[x, y]]) = [[ (x + y), y]]) → linear_transformation T ℝ:=
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

end vector_spaces -- hide