import game.subspace_world.complement_subspace --hide

namespace vector_spaces --hide
open tuple --hide

/-

# Subspace World

Background:

Here we want to prove that the intersection of a subspace V and it's orthogonal complement is the zero vector. 
If Vᗮ is denoted as the orthogonal complement of a subpsace V, then every vector in Vᗮ is orthogonal to every vector in V, and vice versa. 
The intersection of Vᗮ and V must contain vectors that are orthogonal to themselves. Recall, what we learnt in Vector World about a vector being orthogonal to itself. 

Strategy:

Our approach in Lean will be similar, we will have to prove that if some vector y in V is orthogonal to every vector in V, it must be the zero vector, and that 0 is orthogonal to every 
vector in V. 

(Remember, set.eq_of_subset_of_subset tells us that if a is a subset of b and b is a subset of a, then a = b.)



# Level

-/

/- Lemma 
-/

lemma complement_inter_zero {n : ℕ} {V : set (ℝ ^ n)} [v : subspace (ℝ ^ n) ℝ V] : V ∩ (orth_complement V) = {x : ℝ ^ n | x = 0} := 
begin 
  apply set.eq_of_subset_of_subset,   
  { simp, 
    intros y hᵥ h, 
    specialize h y hᵥ, 
    exact (dot_pos_def_2 y).1 h, }, 

  { simp,  
    split, 
    { exact v.contains_zero, }, 
    { intros x hₓ,  
      exact zero_dot x, },
    },
end

end vector_spaces --hide