import game.subspace_world.complement_inter_zero

namespace vector_spaces
open tuple

/-

# Subspace World

Background: V and W are orthogonal. To prove V is a subspace of orth comp of W

# Level


-/

/- Lemma 
-/

lemma orth_subset_orth_complement {n : ℕ} (V : set (ℝ ^ n)) (W : set (ℝ ^ n)) [V_sub : subspace (ℝ ^ n) ℝ V] 
[W_sub : subspace (ℝ ^ n) ℝ W] : orthogonal V W → V ⊆ Wᗮ := 
begin 
  intro h, 
  rw set.subset_def, 
  intros v v_V, 
  simp at *,
  intros w w_W,  
  exact h v w v_V w_W, 
end

end vector_spaces