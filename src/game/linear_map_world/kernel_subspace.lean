import game.linear_map_world.example_1 --hide
namespace vector_spaces
open tuple

/- 

# Linear Transformation world

## Level 6: `The Kernel of a linear transformation is a subspace` 

N(A) is a subspace for any linear transformation A. 

-/

/- Lemma

-/
instance kernel_subspace {n m : ℕ} (T : ℝ ^ n → ℝ ^ m) :
linear_transformation T ℝ → subspace (ℝ ^ n) ℝ (kernel T) :=
begin 
intro h, 
split,
{ intros u hᵤ v hᵥ,
  simp at *,
  specialize h 1 1 u v,  
  repeat {rw tuple.one_smul at h},
  rw [h, hᵤ, hᵥ],     
  simp, }, 

{ intros c v hᵥ,  
  simp at *, 
  specialize h c 0 v 0, 
  repeat {rw zero_smul' at h},
  simp at h, 
  rw [h, hᵥ],
  rw smul_zero', },

{ exact zero_in_kernel T h, },
  

end


end vector_spaces --hide