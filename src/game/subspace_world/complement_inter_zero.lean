import game.subspace_world.complement_subspace

namespace vector_spaces
open tuple


lemma complement_inter_zero {n : ℕ} {V: set (ℝ ^ n)} [v : subspace (ℝ ^ n) ℝ V]: V ∩ (orth_complement V) = {x : ℝ ^ n | x = 0} := 
begin 
  ext, --let x be arbitrary
  split, 
  { intro h, 
  cases h with h₁ h₂, 
  simp at *, 
  have orth_self := h₂ x h₁, 
  exact (dot_pos_def_2 x).1 orth_self,}, 
  {intro h, 
  split, 
  {simp at h, rw h, 
  exact v.contains_zero, }, 
  { have h₁:= vector_spaces.orth_complement_subspace V,
    simp at h, 
    rw h, 
    exact h₁.contains_zero, 
  }, }
end

end vector_spaces