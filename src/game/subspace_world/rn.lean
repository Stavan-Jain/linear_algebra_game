import game.subspace_world.zero --hide 

namespace vector_spaces --hide
open tuple --hide
open set --hide

open set
/- 

# Subspace World

Background: 
Here we will be proving that Rⁿ is a subspace of itself. As before, we must show that 
Rⁿ fulfils the following: 
 1. It contains the 0 vector 
 2. It is closed under addition 
 3. It is closed under scalar multiplication 

Strategy:
In Lean you will also have to show that Rⁿ fulfils these conditions individually.#check
# Level 

-/

/- 
Lemma: 
Rⁿ is a a subspace of itself-/

instance all_rn {n : ℕ} : subspace (ℝ ^ n) ℝ univ := begin 
  split, 
  { intros, simp at *, },
  { intros, simp at *, }, 
  { intros, simp at *, },
end

end vector_spaces --hide
