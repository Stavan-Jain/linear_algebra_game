import game.subspace_world.line

namespace vector_spaces
open tuple

/-

# Subspace World

Background: 
Here we'll proving that the set of all v : ℝ ^ n, such that  a ⬝ v = 0 is a subspace. As before, it must fulfil the following:-
 1. It contains the 0 vector 
 2. It is closed under addition 
 3. It is closed under scalar multiplication 

Recall the properties of the dot product while doing this proof. 

Strategy:
Recall the properties of the dot product you've alread proved in dot product world as you do this proof. 
Good luck!


# Level 4: The set of all vectors v: R ^ n, such that a ⬝ v= 0 is a subspace. 

-/

/- Lemma 
The set of all v : ℝ ^ n, such that  a ⬝ v = 0 is a subspace
-/

instance dot_prod {n : ℕ} {a : ℝ ^ n} : subspace (ℝ ^ n) ℝ {v : ℝ ^ n | a ⬝ v = 0} := 
begin
  split,
  { intros u h₁ v h₂,
    simp at *,
    rw [dot_dist, h₁, h₂],
    simp, },

  { intros c v h,
    simp at *,
    rw [dot_comm, scalar_through, dot_comm, h],
    ring, },
  { simp,
    rw [dot_comm, zero_dot], },
end

end vector_spaces