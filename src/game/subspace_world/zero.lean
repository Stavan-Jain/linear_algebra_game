import vectors.subspace
import game.vector_world.orth_self_unique_zero
import game.auxiliary_theorems.zero_smul
import game.vector_spaces_world.vector_space
namespace vector_spaces
open tuple

/- 
Background: 
Here we will be proving that the zero vector itself is a subspace. As before, we will have to prove that the zero vector fulfils
the following :-
1. It contains the 0 vector 
 2. It is closed under addition 
 3. It is closed under scalar multiplication 


Just 0 is a subspace
-/

instance zero {n : ℕ}: subspace (ℝ ^ n) ℝ {v : ℝ ^ n | v = 0} := begin
  split,
  { intros u h1 v h2, 
    simp at *, 
    rw [h1, h2],
    simp, },

  { intros, 
  simp at *, 
  rw H, rw smul_zero', }, 
  { simp at *, },
end

end vector_spaces