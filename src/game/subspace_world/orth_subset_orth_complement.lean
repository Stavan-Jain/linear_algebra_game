import game.subspace_world.complement_inter_zero

namespace vector_spaces
open tuple


lemma orth_subset_orth_complement 
{n : ℕ} (V: set (ℝ ^ n)) (W: set (ℝ ^ n))
[V_sub : subspace (ℝ ^ n) ℝ V] [W_sub : subspace (ℝ ^ n) ℝ W]: 
orthogonal V W → V ⊆  orth_complement W  := 
begin 
  intro h₁, 
  rw set.subset_def, 
  intros v vV, 
  simp at *,
  intros w wW,  
  exact h₁ v w vV wW, 
end

end vector_spaces