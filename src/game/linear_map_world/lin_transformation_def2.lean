import game.linear_map_world.zero_in_nullspace --hide
namespace tuple -- hide

/- 

# Linear Transformation world

## Level 2: `Equivalent definition of linear transformation` 

We've defined a linear transformation as a map T that satisfies 

T(cx + dy) = cT(x) + dT(y)

for all vectors x, y and scalars c. We're now going to prove that this is equivalent
to the usual definition: 

1. T(x + y) = T(x) + T(y)
2. T(cx) = cT(x)

-/

/- Lemma

-/
lemma lin_transformation_def2 : ∀ {n m : ℕ} (T : ℝ ^ n → ℝ ^ m),
  linear_transformation T ↔ ∀ (c: ℝ) (x y : ℝ ^ n), (T (c• x)) = c • (T x) ∧ T (x + y) = T x + T y :=
begin 
  intros n m T, 
  split, 
  {intro h, intros c x y, 
  split, 
  {
    have h₁ := h c 0 x 0, 
    repeat {rw zero_smul' at h₁},
    simp at h₁,   
    exact h₁, 
  }, 
  have h₁ := h 1 1 x y,
  repeat {rw one_smul at h₁},  
  exact h₁,  
  }, 
  {
    intro h, 
    intros c d x y, 
    have h2 := h c (c• x) (d•y), 
    cases h2 with h3 h4, 
    have h5:=  (h c x y).1, 
    have h6:=  (h d y x).1,
    rw h5 at h4, 
    rw h6 at h4, 
    exact h4, 
  }
  

end

end tuple -- hide