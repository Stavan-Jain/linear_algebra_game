import game.subspace_world.dot_prod

namespace vector_spaces
open tuple

instance inter_subspace {n : ℕ} {U V : set (ℝ ^ n)} [u : subspace (ℝ ^ n) ℝ U] [v : subspace (ℝ ^ n) ℝ V]:
subspace (ℝ ^ n) ℝ (U ∩ V) := 
begin
  split,

  { intros xᵤ hᵤ xᵥ hᵥ, 
    simp at *, 
    split,
    { exact u.closed_add xᵤ hᵤ.1 xᵥ hᵥ.1, },
    { exact v.closed_add xᵤ hᵤ.2 xᵥ hᵥ.2, }, 
    },

  { intros c xᵥ h, 
    simp at *, 
    exact ⟨u.closed_smul c xᵥ h.1, v.closed_smul c xᵥ h.2⟩, },

  { simp at *,
    exact ⟨u.contains_zero, v.contains_zero⟩, },
end

end vector_spaces