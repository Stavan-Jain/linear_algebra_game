import game.linear_map_world.example_1 --hide
namespace vector_spaces
open tuple

/- 

# Linear Transformation world

Background: In this level, you'll first be given the definition of kernel:
The kernel of a linear map, also known as the null space or nullspace, is the linear 
subspace of the domain of the map which is mapped to the zero vector.

That is, for T ∈ L(V, W), the kernel of T is the subset of V consisting of those 
vectors that T maps to 0. That is null T = { v \in V : Tv = 0 }.

In this level, you are going to prove that the kernel of a linear transformation is
a subspace.

Hint: Do similarly as in the previous level. Remember to use the split tactic.

## Level 6: `The Kernel of a linear transformation is a subspace` 

N(A) is a subspace for any linear transformation A. 

-/

/- Lemma
Let T: Rⁿ → Rᵐ be a linear transformation, then kernel(T) is a subspace of Rⁿ
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