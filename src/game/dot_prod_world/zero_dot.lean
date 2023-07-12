import game.dot_prod_world.dot_dist --hide

namespace tuple -- hide

/- 
# Dot Product World

Background:
 Here we'll be proving that the dot product of the zero vector with any vector x is 0. This follows from the definition of the dot product. 

 Strategy:
 As seen before, it may make sense to begin with induction, and first prove that 0 ⬝ x = 0  for x equal to the zero vector. 
 Good luck!

## Level 5: `zero dot vector equals zero` 

-/

/- Lemma
||(1 / ||x|| ) *x || = 1
-/


lemma zero_dot: ∀ {n : ℕ} (x : ℝ ^ n), 0 ⬝ x = 0 :=
begin 
   intros n x, 
   induction n with d hd, 
   { cases x, 
     simp, },
   { cases x with n head tail, 
     simp, 
     exact hd tail, },
end

end tuple -- hide
