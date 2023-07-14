import game.subspace_world.orth_subset_orth_complement -- hide

namespace vector_spaces -- hide
open tuple -- hide

/-

# Subspace World

Background:
Here we will be proving that if V is a subset of W, then Wᗮ is a subset of Vᗮ i.e. that every wᗮ in Wᗮ belongs to Vᗮ. Under what condition would every element in Wᗮ belong to Vᗮ? 
As we know, every vᗮ in Vᗮ is orthongal to every v in V, and every wᗮ in Wᗮ is orthogonal to every w in W. If V is a subset of W then every element v in V also belongs to W.  
Think about what this means for the relationship between every element in Wᗮ and every element in V, and hence the relationship between every element in Wᗮ and Vᗮ as you do this proof. 

Strategy:
Remember, set.subset_def allows us to say that if  s ⊆ t, then for every x ∈ s → x ∈ t. 
Also, keep in mind that "simp at *"  simplifies all current hypotheses and the current goal, which here may help in relating the definition of 
orthogonality with the dot product. 

# Level 9: If V  ⊆ W then Wᗮ ⊆ Vᗮ 

-/

/- Lemma 
V  ⊆ W → Wᗮ ⊆ Vᗮ
-/


lemma orth_complement_subset {n : ℕ} (V : set (ℝ ^ n)) (W : set (ℝ ^ n)) [V_sub : subspace (ℝ ^ n) ℝ V] 
[W_sub : subspace (ℝ ^ n) ℝ W] : V ⊆ W → Wᗮ ⊆ Vᗮ := 
begin 
  intro v_sub_w, 
  rw set.subset_def, 
  intros w w_W v v_V, 
  exact w_W v (v_sub_w v_V),  
end

end vector_spaces -- hide
