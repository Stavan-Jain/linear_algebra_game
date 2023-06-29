import vectors.subspace

namespace vector_spaces
open tuple

instance line_through_origin {n : ℕ}: subspace (ℝ ^ n) ℝ univ  := begin 
  constructor, 
  {
    intros, simp at *,  
  } ,
  {
    intros, simp at *,  
  }, 
  {
    intros, simp at *, 
  },
end

end vector_spaces