import vectors.tuple -- hide
import data.real.basic
import game.vector_world.level14 --hide

namespace tuple -- hide

/- 
# Vector world

## Level 15: `zero dot vector equals zero` 

-/

/- Lemma

0 ⬝ x = 0 

Here we'll be proving that the dot product of the zero vector with any vector x is zero. We know that 
if the dot product of x and y is zero, then the two vectors are orthogonal. We also know that zero is orthogonal 
to every vector. Therefore it must follow that 0 ⬝ x = 0.

Strategy:

We'll be proving this using induction.

Hint:

Remember, applying cases to any vector x of length n breaks it into a head and a tail-- with the head being a single element 
and the tail being a tuple of length n-1. If we already know that 0 ⬝ x = 0 is true for a vector of length n, how can we use it to show that it 
must be true for a vector of length n+1?

-/


lemma zero_dot: ∀ {n : ℕ} (x : ℝ ^ n), 0 ⬝ x = 0 :=
begin 
   intro n , 
   induction n with d hd, 
   intro x, 
   cases x, 
   dsimp [tuple.zero, dot_product], refl, 
   intro x, 
   cases x, 
   dsimp [tuple.zero, dot_product], simp, 
   exact hd x_tail,  
end

end tuple -- hide
