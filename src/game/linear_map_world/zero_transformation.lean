import game.linear_map_world.id_transformation
namespace vector_spaces -- hide
open tuple

/- 

# Linear Transformation world

## Level 4: `T(v) = 0 is a linear transformation` 

-/

/- Lemma

-/
lemma zero_transformation : ∀ {n : ℕ} (T : ℝ ^ n  → ℝ ^ n),
  (∀ (v : ℝ ^ n), (T v) = (0 : ℝ ^ n)) → linear_transformation T ℝ :=
begin 
  intros n T h,
  simp,
  intros c d u v,
  repeat {rw h},
  repeat {rw smul_zero'},
  simp, 
end

end vector_spaces -- hide