import game.subspace_world.inter_subspace

namespace vector_spaces
open tuple

instance add_subspace {n : ℕ} {U V : set (ℝ ^ n)} [u: subspace (ℝ ^ n) ℝ U] [v : subspace (ℝ ^ n) ℝ V]: subspace (ℝ ^ n) ℝ {x : ℝ ^ n | ∃ u : U, ∃ v : V, x = u + v}:= 
begin
  split,

  { intros x₁ x₁S x₂ x₂S,  
  simp at *, 
  rcases x₁S with ⟨u₁, u₁U, v₁, v₁V, H₁⟩ , 
  rcases x₂S with ⟨u₂, u₂U, v₂, v₂V, H₂⟩ ,
  use (u₁ + u₂), 
  split, 
  {exact u.1 u₁ u₁U u₂ u₂U,},
  use (v₁ + v₂), 
  split, 
  {exact v.1 v₁ v₁V v₂ v₂V, }, 
  rw [H₁, H₂], 
  rw vec_assoc, 
  nth_rewrite 1 vec_comm, rw vec_assoc,
  nth_rewrite 2 vec_comm, rw ←vec_assoc,     
  },

  {  intros c x xS, 
  simp at *, 
  rcases xS with ⟨ u₁, uU, v₁, vV, H⟩, 
  have cU : c • u₁ ∈ U, 
  { exact u.2 c u₁ uU,},
  have cV : c • v₁ ∈ V,
  { exact v.2 c v₁ vV}, 
  use [c • u₁, cU, c • v₁, cV], 
  rw H,
  rw scalar_dist_1,  
  },

  { simp, 
  use [0 , u.3, 0,v.3],
  simp, },
end

end vector_spaces