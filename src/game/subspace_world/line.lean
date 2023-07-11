import game.subspace_world.rn

namespace vector_spaces
open tuple
open set

instance line_through_origin {n : ℕ} (v : ℝ ^ n) : subspace (ℝ ^ n) ℝ {x : ℝ ^ n | ∃(c : ℝ), x = c • v} := 
begin 
  split, 

  { intros xᵤ hᵤ xᵥ hᵥ,
    -- simp at *,
    cases hᵤ with c₁ hᵤ,
    cases hᵥ with c₂ hᵥ, 
    use (c₁ + c₂), 
    rw [hᵤ, hᵥ, vector_dist], },

  { intros c xᵥ hᵥ,   
    cases hᵥ with c₁ hᵥ,
    rw hᵥ, 
    use (c * c₁),
    rw scalar_assoc, },
 
  { use 0,
    rw zero_smul', },
end

end vector_spaces