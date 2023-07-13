import game.linear_map_world.zero_in_kernel --hide
open tuple
namespace vector_spaces -- hide

/- 

# Linear Transformation world

## Level 2: `Equivalent definition of linear transformation` 

Background: We've defined a linear transformation as a map T that satisfies 
T(cx + dy) = cT(x) + dT(y) for all vectors x, y and scalars c. 
We're now going to prove that this is equivalent to the usual definition
which has been mentioned before: 
1. T(x + y) = T(x) + T(y)
2. T(cx) = cT(x)

Hint: Remember to use theorem zero_smul' and tuple.one_smul!

-/

/- Lemma
T(cx + dy) = cT(x) + dT(y) ↔ T(x + y) = T(x) + T(y), T(cx) = cT(x)
-/
lemma lin_transformation_def2 : ∀ {n m : ℕ} (T : ℝ ^ n → ℝ ^ m),
linear_transformation T ℝ ↔ ∀ (c : ℝ) (x y : ℝ ^ n), (T (c • x)) = c • (T x) ∧ T (x + y) = T x + T y :=
begin 
  intros n m T, 
  split, 

  { intros h c x y, 
    split, 
    { specialize h c 0 x 0, 
      repeat {rw zero_smul' at h},
      simp at h,   
      exact h, }, 
    { specialize h 1 1 x y,
      repeat {rw tuple.one_smul at h},  
      exact h, },
  }, 

  { intros h c d x y,
    have hc := (h c x y).1,
    have hd := (h d y x).1,
    have hT := (h c (c • x) (d • y)).2,
    rw [hT, hc, hd], },
end

end vector_spaces -- hide