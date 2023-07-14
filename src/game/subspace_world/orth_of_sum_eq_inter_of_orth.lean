import game.subspace_world.orth_complement_subset --hide
namespace vector_spaces --hide
open tuple --hide

/-

# Subspace World

Background: 
Here we will be proving that, given two subspaces U and V, the orthogonal complement of U + V is the intersection of Uᗮ and Vᗮ.
Every element in (U+V)ᗮ should be orthogonal to every element in U _and_ every element in V. What can we conclude from this? Let
us see how we can go about doing this proof in Lean. 

Strategy:

Remember the following:

1. Another way of showing that A=B is by saying that A ⊆ B and B ⊆ A. The way to represent this in Lean is using 
set.eq_of_subset_of_subset.

2. "simp at *"  simplifies all current hypotheses and the current goal. It shows what you need to do prove a goal.

3. The tactic specialize h a₁ ... aₙ works on local hypothesis h. The premises of this hypothesis, either universal 
quantifications or non-dependent implications, are instantiated by concrete terms coming either from arguments a₁ ... aₙ. 
The tactic adds a new hypothesis with the same name h := h a₁ ... aₙ and tries to clear the previous one.

# Level 11: Proving that (U+V)ᗮ = Uᗮ ∩ Vᗮ

-/

/- Lemma 
(U+V)ᗮ = Uᗮ ∩ Vᗮ
-/

lemma orth_of_sum_eq_inter_of_orth {n : ℕ} (U : set (ℝ ^ n)) (V : set (ℝ ^ n)) [U_sub : subspace (ℝ ^ n) ℝ U] [V_sub : subspace (ℝ ^ n) ℝ V] : 
({x : ℝ ^ n | ∃ u : U, ∃ v : V, x = u + v})ᗮ = Uᗮ ∩ Vᗮ := 
begin 
  apply set.eq_of_subset_of_subset,

  { intros x h,
    simp at *,
    split,
    { intros u u_pos,
      exact h u u u_pos 0 V_sub.contains_zero (by simp), },
    { intros v v_pos,
      exact h v 0 U_sub.contains_zero v v_pos (by simp), }, 
    },

  { intros x h,
    cases h with h₁ h₂,
    simp at *,
    intros v x₁ x₁_pos x₂ x₂_pos hᵥ,
    specialize h₁ x₁ x₁_pos,
    specialize h₂ x₂ x₂_pos,
    rw [hᵥ, dot_dist, h₁, h₂],
    simp, },

end

end vector_spaces --hide