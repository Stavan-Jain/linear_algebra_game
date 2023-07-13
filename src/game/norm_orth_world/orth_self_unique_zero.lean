import game.norm_orth_world.norm_neg_eq_neg --hide

namespace tuple -- hide

/- 
# Norm Orth World

Background:
Here we'll be proving that the zero vector is the only vector orthogonal to itself. It may be helpful to come back to R² and imagine two orthogonal vectors. It is easy to see that
a vector of some non zero length can never be orthogonal to itself. Also, by definition, two vectors x and y are orthogonal if their dot product is 0. We also know that the dot product of x
with itself gives the square of it's magnitude. This is enough information to conclude that the zero vector is the only vector that is perpendicular to itself.
Now let us see how to approach this proof formally.


Strategy:
Remember that the dot product is positive definite. Think about how you can use that fact in this proof.


## Level 2: `**0** is uniquely orthogonal to itself` 

-/

/- Lemma
**0** is the only vector orthogonal to itself
-/

lemma orth_self_unique_zero : ∀ {n : ℕ} (x : ℝ ^ n),  x ⟂ x → x = 0 :=
begin 
  intros n x perp,
  simp at perp,
  rwa dot_self_zero at perp,
end

end tuple --hide
