import game.subspace_world.inter_subspace --hide

namespace vector_spaces --hide
open tuple --hide
/-
# Subspace World

Background:\  

Here we will prove that given subspaces U and V, U+V is also a subspace. We know that for U+V to be a subspace, it must fulfil the following conditions: 
1. it must contain 0 
2. it must be be closed under addition 
3. it must be closed under scalar multiplicaiton. 
Let us imagine that for some x1:(U+V), x₁= u₁ + v₁ for some u₁: U and v₁:V, and that for some other x₂:(U+V) x₂= u₂+v₂ for some u₂:U and v₂:V. 
If we can prove that x1+x2 is a part of U+V and that cx₁ is a part of U+V, then that is enough to show that U+V is also a subspace. 

Strategy:
rcases is a tactic that will perform cases recursively, according to a pattern. It is used to destructure hypotheses or expressions composed 
of inductive types like h1 : a ∧ b ∧ c ∨ d or h2 : ∃ x y, trans_rel R x y
(rcases applies cases repeatedly to every hypothesis that is being generated.) 

# Level 6: For subspaces U and V, U + V is also a subspace of R^n 
-/


/- Lemma:
U + V is also a subspace of R^n 
-/

instance add_subspace {n : ℕ} {U V : set (ℝ ^ n)} [u : subspace (ℝ ^ n) ℝ U] [v : subspace (ℝ ^ n) ℝ V] :
subspace (ℝ ^ n) ℝ {x : ℝ ^ n | ∃ u : U, ∃ v : V, x = u + v} := 
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
    rw [H, scalar_dist_1], },

  { simp, 
    use [0 , u.contains_zero, 0,v.contains_zero],
    simp, },
end

end vector_spaces