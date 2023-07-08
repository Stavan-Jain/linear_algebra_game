import game.subspace_world.complement_inter_zero

namespace vector_spaces
open tuple


lemma orth_subset_orth_complement {n : ℕ} (V : set (ℝ ^ n)) (W : set (ℝ ^ n)) [V_sub : subspace (ℝ ^ n) ℝ V] 
[W_sub : subspace (ℝ ^ n) ℝ W]: orthogonal V W → V ⊆ orth_complement W := 
begin 
  intro h, 
  rw set.subset_def, 
  intros v v_V, 
  simp at *,
  intros w w_W,  
  exact h v w v_V w_W, 
end

end vector_spaces