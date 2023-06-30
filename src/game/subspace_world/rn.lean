import vectors.subspace
import game.subspace_world.zero

namespace vector_spaces
open tuple
open set

open set

instance all_rn {n : ℕ}: subspace (ℝ ^ n) ℝ univ  := begin 
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