import game.subspace_world.orth_complement_subset
namespace vector_spaces
open tuple

/-

# Subspace World

Background: 
Here we will be proving that, given two subspaces U and V, the orthogonal complement of U + V is the intersection of Uᗮ and Vᗮ.
Every element in (U+V)ᗮ should be orthogonal to every element in U _and_ every element in V. What can we conclude from this? Let
us see how we can go about doing this proof in Lean. 

Strategy:
Let's take a minute to get introduced to a tactic called ext. "ext" applies as many extensionality lemmas as possible; 

# Proving that (U+V)ᗮ = Uᗮ ∩ Vᗮ


-/

/- Lemma 
(U+V)ᗮ = Uᗮ ∩ Vᗮ
-/

lemma orth_of_sum_eq_inter_of_orth {n : ℕ} (U: set (ℝ ^ n)) (V: set (ℝ ^ n))
[U_sub : subspace (ℝ ^ n) ℝ U] [V_sub : subspace (ℝ ^ n) ℝ V]: 
orth_complement ({x : ℝ ^ n | ∃ u : U, ∃ v : V, x = u + v}) = orth_complement U ∩ orth_complement V := 
begin 
  ext x,
  split,
  { intro h,
    simp at *,
    split,
    { intros u u_pos,
      specialize h u u u_pos 0 V_sub.contains_zero (by simp), -- explain specialize
      exact h, },
    { intros v v_pos,
      specialize h v 0 U_sub.contains_zero v v_pos (by simp),
      exact h,}, 
    },

  { intro h,
    cases h with h₁ h₂,
    simp at *,
    intros v x₁ x₁_pos x₂ x₂_pos hᵥ,
    specialize h₁ x₁ x₁_pos,
    specialize h₂ x₂ x₂_pos,
    rw [hᵥ, dot_dist, h₁, h₂],
    simp, },

end

end vector_spaces