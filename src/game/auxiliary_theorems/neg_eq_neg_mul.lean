import game.auxiliary_theorems.zero_smul
namespace tuple -- hide

/- 

# Vector world

Let's come back to thinking about what the dot product describes. It gives us an idea for how much one vector aligns with another. 
The amount that a vector aligns with itself can only be zero if it itself is the zero vector. 

We're going to prove that if dot product of a vector with itself is 0 then it must be the zero vector. 

## Level 6 : `neg_eq_neg_mul` 

-/

/- Lemma
x ⬝ x = 0 ↔ x = tuple.zero
-/
lemma neg_eq_neg_mul : ∀ {n : ℕ} (x : ℝ ^ n), -x = (-1 : ℝ) • x :=
begin 
  intros n x,
  induction n with n hn,
  { cases x, 
    refl, },
  { cases x with n x₁ xₙ,
    simp,
    exact hn xₙ, },
end

end tuple -- hide
