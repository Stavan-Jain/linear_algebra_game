import game.linear_map_world.lin_transformation_def2 --hide
namespace vector_spaces
open tuple

/- 

# Linear Transformation world

## Level 3: `The Null Space of a linear transformation is a subspace` 

N(A) is a subspace for any linear transformation A. 

-/

/- Lemma

-/
instance kernel_subspace {n m : ℕ} (T : ℝ ^ n → ℝ ^ m):
  linear_transformation T →   subspace (ℝ^ n) ℝ (kernel T):=
begin 
intro h₁, 
split, 
{
  intros u u_in_ns v v_in_ns,
  simp at *,
  have h₂ := h₁ 1 1 u v,  
  repeat {rw tuple.one_smul at h₂},
  rw [u_in_ns, v_in_ns] at h₂,     
  simp at h₂, 
  exact h₂,  
}, 
{
  intros c x h₂,  
  simp at *, 
  have h₃ := h₁ c 0 x 0, 
  repeat {rw zero_smul' at h₃},
  rw h₂ at h₃, 
  simp at h₃, 
  rw smul_zero' at h₃, 
  exact h₃,   
}, 
{
  exact zero_in_kernel T h₁,  
}
  

end


end vector_spaces --hide