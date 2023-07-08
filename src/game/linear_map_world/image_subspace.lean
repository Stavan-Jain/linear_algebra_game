import game.linear_map_world.kernel_subspace --hide
namespace vector_spaces
open tuple

/- 

# Linear Transformation world

## Level 7: `The Image of a linear transformation is a subspace` 

C(A) is a subspace for any linear transformation A. 

-/

/- Lemma

-/
instance image_subspace {n m : ℕ} (T : ℝ ^ n → ℝ ^ m):
  linear_transformation T ℝ → subspace (ℝ^ m) ℝ (image T) :=
begin 
  intro h, 
  split,
  { intros u hᵤ v hᵥ,
    cases hᵤ with x₁ Tx₁,
    cases hᵥ with x₂ Tx₂, 
    use (x₁ + x₂),
    specialize h 1 1 x₁ x₂,
    repeat {rw tuple.one_smul at h},
    rw [h, Tx₁, Tx₂], },
  
  { intros c v hᵥ,
    cases hᵥ with x Tx, 
    specialize h c 0 x 0,
    repeat {rw zero_smul' at h},
    simp at *,
    use (c • x),
    rw [h, Tx], },

  { use 0,  
    exact zero_in_kernel T h, },
end


end vector_spaces --hide