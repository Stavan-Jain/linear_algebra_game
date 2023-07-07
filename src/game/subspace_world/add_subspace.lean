import game.subspace_world.inter_subspace

namespace vector_spaces
open tuple

instance add_subspace {n : ℕ} {U V : set (ℝ ^ n)} [u : subspace (ℝ ^ n) ℝ U] [v : subspace (ℝ ^ n) ℝ V] :
subspace (ℝ ^ n) ℝ {x : ℝ ^ n | ∃ u : U, ∃ v : V, x = u + v}:= 
begin
  split,

  { intros xᵤ hᵤ xᵥ hᵥ,
    simp at *, 
    rcases hᵤ with ⟨u₁, u₁_U, v₁, v₁_V, H₁⟩, 
    rcases hᵥ with ⟨u₂, u₂_U, v₂, v₂_V, H₂⟩,
    use (u₁ + u₂), 
    split, 
    { exact u.closed_add u₁ u₁_U u₂ u₂_U, },
    { use (v₁ + v₂), 
      split, 
      { exact v.closed_add v₁ v₁_V v₂ v₂_V, }, 
      { rw [H₁, H₂], 
        rw vec_assoc, 
        nth_rewrite 1 vec_comm, rw vec_assoc,
        nth_rewrite 2 vec_comm, rw ←vec_assoc, },
      },
    },

  { intros c xᵥ hᵥ, 
    simp at *, 
    rcases hᵥ with ⟨u₁, u_U, v₁, v_V, H⟩, 
    have c_U := u.closed_smul c u₁ u_U,
    have c_V := v.closed_smul c v₁ v_V,
    use [c • u₁, c_U, c • v₁, c_V], 
    rw H,
    rw scalar_dist_1,  
    },

  { simp, 
    use [0 , u.contains_zero, 0,v.contains_zero],
    simp, },
end

end vector_spaces