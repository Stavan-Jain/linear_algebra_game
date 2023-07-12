import game.linear_map_world.lin_transformation_def2
namespace vector_spaces -- hide

/- 

# Linear Transformation world

## Level 3: `T(v) = v is a linear transformation` 

-/

/- Lemma

-/
lemma id_transformation : ∀ {n : ℕ} (T : ℝ ^ n  → ℝ ^ n),
  (∀ (v : ℝ ^ n), (T v) = v) → linear_transformation T ℝ :=
begin 
  intros n T h,
  simp,
  intros c d u v,
  repeat {rw h},
end

end vector_spaces -- hide