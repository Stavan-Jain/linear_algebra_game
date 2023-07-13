import game.subspace_world.complement_inter_zero --hide 

namespace vector_spaces --hide
open tuple --hide

/-

# Subspace World

Background: 

Here we are going to prove that if V and W are orthogonal subspaces, then V is a subset of orthogonal component of W.
If V and W are orthogonal subspaces then every vector in W is orthogonal to every vector in V. W may or may not contain 
every vector that is orthogonal to all the vectors in V, and vice versa. This means that V must be a subset of the orthogonal
complement of W.

Strategy:
Remember, how a subset is defined in Lean, (Hint: set.subset_def says that if x ⊆ t then a ∈ x → a ∈ t.)
and how to express that if V⊆ Wᗮ every v ∈ V must be ⟂ to every w ∈ W. 

# Level : V ⟂ W → V ⊆ Wᗮ 

-/

/- Lemma 
V ⟂ W → V ⊆ Wᗮ 
-/

lemma orth_subset_orth_complement {n : ℕ} (V : set (ℝ ^ n)) (W : set (ℝ ^ n)) [V_sub : subspace (ℝ ^ n) ℝ V] 
[W_sub : subspace (ℝ ^ n) ℝ W] : orthogonal V W → V ⊆ orth_complement W := 
begin 
  intro h, 
  rw set.subset_def, 
  intros v v_V, 
  simp at *,
  intros w w_W,  
  exact h v w v_V w_W, 
end

end vector_spaces --hide