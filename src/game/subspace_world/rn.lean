import game.subspace_world.zero

namespace vector_spaces
open tuple
open set

open set
/- 
Background: Rn is a subspace of itself-/

instance all_rn {n : ℕ}: subspace (ℝ ^ n) ℝ univ  := begin 
  split, 
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