import game.subspace_world.add_subspace

namespace vector_spaces
open tuple


instance orth_complement_subspace {n : ℕ} (V: set (ℝ ^ n)) [v : subspace (ℝ ^ n) ℝ V]: subspace (ℝ ^ n) ℝ (orth_complement V) := 
begin
  split, 

  { intros xᵤ hᵤ xᵥ hᵥ,
    simp at *,
    intros v₁ v₁_V, 
    rw [dot_comm, dot_dist, dot_comm], 
    nth_rewrite 1 dot_comm,   
    rw hᵤ v₁ v₁_V, 
    rw hᵥ v₁ v₁_V, 
    simp, }, 

  { intros c xᵥ hᵥ, 
    simp at *,
    intros v₁ v₁_V, 
    rw scalar_through,
    rw hᵥ v₁ v₁_V, 
    simp, },

  { simp, 
    intros v₁ v₁_V, 
    rw zero_dot, },
end

end vector_spaces