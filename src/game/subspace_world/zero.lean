import vectors.subspace --hide
import game.norm_orth_world.triangle_ineq --hide
import game.vector_spaces_world.vector_space --hide
namespace vector_spaces --hide
open tuple --hide 

/- 
# Subspace World
Background: 
Here we will be proving that the set containing only the zero vector is a subspace. We will have to prove that this set fulfils
the following :-
 1. It contains the 0 vector 
 2. It is closed under addition 
 3. It is closed under scalar multiplication 

Strategy:
Using split at the beginning will split the goal into the three conditions needed to prove that {0} is a subspace of R^n. 

Hint:

tuple.smul_zero' : ∀ {n : ℕ} (c : ℝ), c • 0 = 0

# Level 1: {0} is a subspace of Rⁿ 
-/

/- 
Lemma: 
0 is a subsapce of Rⁿ 
-/

instance zero {n : ℕ}: subspace (ℝ ^ n) ℝ {v : ℝ ^ n | v = 0} := begin
  split,

  { intros u h1 v h2, 
    simp at *, 
    rw [h1, h2],
    simp, },

  { intros, 
    simp at *, 
    rw [H, smul_zero'], }, 
    
  { simp at *, },
end

end vector_spaces --hide