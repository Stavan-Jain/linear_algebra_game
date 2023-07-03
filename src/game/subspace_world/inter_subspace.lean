import game.subspace_world.dot_prod

namespace vector_spaces
open tuple

instance inter_subspace {n : ℕ} {U V : set (ℝ ^ n)} [u: subspace (ℝ ^ n) ℝ U] [v : subspace (ℝ ^ n) ℝ V]: subspace (ℝ ^ n) ℝ (U ∩ V):= 
begin
  split,

  { intros xᵤ hᵤ xᵥ hᵥ, 
    simp at *, 
    exact ⟨u.closed_add xᵤ hᵤ.left xᵥ hᵥ.left, 
    v.closed_add xᵤ hᵤ.right xᵥ hᵥ.right⟩, },

  { intros c xᵥ h, 
    simp at *, 
    exact ⟨u.closed_smul c xᵥ h.left, v.closed_smul c xᵥ h.right⟩, },

  { simp at *,
    exact ⟨u.contains_zero, v.contains_zero⟩, },
end

end vector_spaces