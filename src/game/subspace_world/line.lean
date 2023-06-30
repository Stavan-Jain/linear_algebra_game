import vectors.subspace
import game.subspace_world.rn

namespace vector_spaces
open tuple

instance line_through_origin {n : ℕ} (v : ℝ ^ n): subspace (ℝ ^ n) ℝ {x : ℝ ^ n |∃(c : ℝ), x = c • v}  := begin 
  constructor, 
  {
    intros, simp at *,
    cases H with c1 H1,
    cases H_1 with c2 H2, 
    use (c1 + c2), 
    rw [H1, H2], sorry, 

  } ,
  {
    intros, simp at *, sorry, 
  }, 
  {
    intros, simp at *, sorry,  
  },
end

end vector_spaces