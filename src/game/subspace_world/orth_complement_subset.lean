import game.subspace_world.orth_subset_orth_complement

namespace vector_spaces
open tuple


lemma orth_complement_subset {n : ℕ} (V : set (ℝ ^ n)) (W : set (ℝ ^ n)) [V_sub : subspace (ℝ ^ n) ℝ V] 
[W_sub : subspace (ℝ ^ n) ℝ W]: V ⊆ W → orth_complement W ⊆ orth_complement V := 
begin 
  intro v_sub_w, 
  rw set.subset_def, 
  intros w w_W v v_V, 
  exact w_W v (v_sub_w v_V),  
end

end vector_spaces