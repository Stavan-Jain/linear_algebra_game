import game.subspace_world.complement_subspace

namespace vector_spaces
open tuple


lemma complement_inter_zero {n : ℕ} {V : set (ℝ ^ n)} [v : subspace (ℝ ^ n) ℝ V] : V ∩ (orth_complement V) = {x : ℝ ^ n | x = 0} := 
begin 
  apply set.eq_of_subset_of_subset,   
  { simp, 
    intros y y_in_V h₁, 
    have orth_self := h₁ y y_in_V, 
    exact (dot_pos_def_2 y).1 orth_self, }, 

  { simp,  
    split, 
    { exact v.contains_zero, }, 
    { have h₁:= vector_spaces.orth_complement_subspace V,
      intros x x_in_V,  
      exact zero_dot x, },
    },
end

end vector_spaces