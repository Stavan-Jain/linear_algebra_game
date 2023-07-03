import game.subspace_world.complement_inter_zero

namespace vector_spaces
open tuple


lemma orth_subset_orth_complement 
{n : ℕ} (V: set (ℝ ^ n)) (W: set (ℝ ^ n))
[v : subspace (ℝ ^ n) ℝ V] [w : subspace (ℝ ^ n) ℝ W]: 
orthogonal V W → V ⊂ orth_complement W  := 
begin 
  sorry, 
end

end vector_spaces