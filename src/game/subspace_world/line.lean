import vectors.subspace
import game.subspace_world.rn
import game.vector_spaces_world.vector_space
import game.vector_world.zero_smul

namespace vector_spaces
open tuple
open set

instance line_through_origin {n : ℕ} (v : ℝ ^ n): subspace (ℝ ^ n) ℝ {x : ℝ ^ n |∃(c : ℝ), x = c • v}  := begin 
  constructor, 
  { intros u h₁ w h₂,
    simp at *,
    cases h₁ with c₁ h₁,
    cases h₂ with c₂ h₂, 
    use (c₁ + c₂), 
    rw [h₁, h₂, scalar_dist_2], } ,

  { intros c₁ u h,
    simp at *,
    cases h with c₂ h,
    rw h,
    use (c₁ * c₂),
    rw scalar_assoc, }, 

  { simp,
    use 0,
    rw zero_smul v, /- explain ambiguous overload-/ },
end

end vector_spaces