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
  linear_transformation T ℝ →  subspace (ℝ^ m) ℝ (image T):=
begin 
  intro h₁, 
  split, 
  {
    intros u u_in_image v v_in_image,
    simp at *, 
    cases u_in_image with x₁ Tx₁, 
    cases v_in_image with x₂ Tx₂,   
    use (x₁ + x₂), 
    have h₂ := h₁ 1 1 x₁ x₂, 
    repeat {rw tuple.one_smul at h₂},
    rw h₂, 
    rw [Tx₁ , Tx₂], 
  }, 
  {
    intros c v v_in_image,
    simp at *,
    cases v_in_image with x Tx,
    use (c • x),
    have h₂:= h₁ c 0 x 0,  
    repeat {rw zero_smul' at h₂}, 
    simp at h₂,   
    rw h₂, 
    rw Tx, 
  }, 
  {
    simp at *, 
    use 0,  
    exact zero_in_kernel T h₁,  
  }
end


end vector_spaces --hide