import game.subspace_world.rn

namespace vector_spaces
open tuple
open set

instance line_through_origin {n : ℕ} (v : ℝ ^ n): subspace (ℝ ^ n) ℝ {x : ℝ ^ n |∃(c : ℝ), x = c • v}  := begin 
  constructor, 
  {
    intros, simp at *,
    cases H with c1 H1,
    cases H_1 with c2 H2, 
    use (c1 + c2), 
    rw [H1, H2], rw vector_dist, 
  } ,
  {
    intros, 
    simp at *,  
    cases H with c2 H,
    rw H, 
    use (c * c2),
    rw scalar_assoc,  
  }, 
  {
    intros, simp at *, use 0, rw zero_smul',    
  },
end

end vector_spaces