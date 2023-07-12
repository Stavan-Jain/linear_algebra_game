import game.subspace_world.complement_subspace

namespace vector_spaces
open tuple


lemma complement_inter_zero {n : ℕ} {V : set (ℝ ^ n)} [v : subspace (ℝ ^ n) ℝ V] : V ∩ (orth_complement V) = {x : ℝ ^ n | x = 0} := 
begin 
  apply set.eq_of_subset_of_subset,   
  { simp, 
    intros y hᵥ h, 
    specialize h y hᵥ, 
    exact (dot_self_zero y).1 h, }, 

  { simp,  
    split, 
    { exact v.contains_zero, }, 
    { intros x hₓ,  
      exact zero_dot x, },
    },
end

end vector_spaces