import game.linear_map_world.id_transformation
namespace vector_spaces -- hide
open tuple

/- 

# Linear Transformation world

Background: Recall the definition of zero mentioned in the level id_transformation.
That is T \in L(V, W) defined by T v = 0.

In this level, you are going to prove that the zero defined above is a linear 
transformation.

Hint: Recall level id_transformation and do this similarly.

## Level 4: `T(v) = 0 is a linear transformation` 

-/

/- Lemma
T: Rⁿ → Rⁿ defined by T(v) = 0 ∀v ∈ Rⁿ is a linear transformation
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