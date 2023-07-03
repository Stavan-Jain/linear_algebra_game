import game.subspace_world.add_subspace

namespace vector_spaces
open tuple


instance orth_complement_subspace {n : ℕ} (V: set (ℝ ^ n)) [v : subspace (ℝ ^ n) ℝ V]: subspace (ℝ ^ n) ℝ (orth_complement V) := 
begin
  split, 
  {
    intros x₁ x₁Vp x₂ x₂Vp,
    simp at *,
    intros x xV, 
    rw [dot_comm, dot_dist], 
    rw dot_comm,
    nth_rewrite 1 dot_comm,   
    rw x₁Vp x xV, rw x₂Vp x xV, 
    simp,  
  }, 
  {
    intros c x₁ x₁Vp, 
    simp at *,
    intros x xV, 
    rw scalar_through,
    rw x₁Vp x xV, 
    simp,  
  },
  {
    simp, intros x xV, rw zero_dot,  
  }
end

end vector_spaces