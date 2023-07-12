import game.subspace_world.rn

namespace vector_spaces
open tuple
open set

/- 
Background: 
Here we'll be proving that any line through the origin, x = c • v, is a subspace. As before, this means that a line through the origin must 
fulfil the following :-
1. It contains the 0 vector 
2. It is closed under addition 
3. It is closed under scalar multiplication

Any line through the origin by defintion contains the 0 vector. It is also easy to imagine that 
if two vectors contained by the line are added, their summation is also contained in the line. Further, 
if a vector contained in the line is multiplied by a scalar, it is also a part of the line. Therefore it must be a subspace. 
Now let us see how to approach this proof is lean!

Strategy:

As before, we will have to prove that a line through the origin fulfils the three defining conditions for a subspace.
Cases!


-/

instance line_through_origin {n : ℕ} (v : ℝ ^ n): subspace (ℝ ^ n) ℝ {x : ℝ ^ n |∃(c : ℝ), x = c • v}  := 
begin 
  split, 
  {
    intros, simp at *,
    cases H with c1 H1,
    cases H_1 with c2 H2, 
    use (c1 + c2), 
    rw [H1, H2], rw vector_dist, 
  } ,
  {
    intros, 
    simp at *,  
    cases H with c2 H,
    rw H, 
    use (c * c2),
    rw scalar_assoc,  
  }, 
  {
    intros, simp at *, use 0, rw zero_smul',    
  },
end

end vector_spaces