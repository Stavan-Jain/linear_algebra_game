import game.dot_prod_world.dot_zero --hide
namespace tuple -- hide

/- 
# Vector world

Now we're gonna try and prove that the dot product is positive definite. 
Positive definiteness relates to symmetric matrices (A is symmetric if A and A^T are equal.)
A symmetric matrix A is said to be positive definite if, for any non-zero vector of dimension equal to A, 
x^T A x is always positive. 

What does this have to do with the dot product?

We can treat the dot product itself as a matrix of one element. On computing x^T A x such that x 
is a vector with one element, the product is always positive.


We're going to prove that the dot product is positive definite!

## Level 5: `dot product is postive definite ` 

-/

/- Lemma
x ⬝ x ≥ 0 ∀x ∈ Rⁿ 
-/
lemma dot_self_nonneg : ∀ {n : ℕ} (x : ℝ ^ n), x ⬝ x ≥ 0 :=
begin 
  intros n x, 
  induction n with d hd,
  { cases x, 
    simp, },
  { cases x with head tail, 
    simp,
    have i := mul_self_nonneg tail, 
    have j := hd x_tail, 
    exact add_nonneg i j, },
end

end tuple -- hide
