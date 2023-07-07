import vectors.tuple -- hide
import data.real.basic
import game.vector_world.dot_comm --hide
namespace tuple -- hide

/- 

Now we're gonna try and prove that the dot product is positive definite. 
Positive definiteness relates to symmetric matrices (A is symmetric if A and A^T are equal.)
A symmetric matrix A is said to be positive definite if, for any non-zero vector of dimension equal to A, 
x^T A x is always positive. 

What does this have to do with the dot product?

We can treat the dot product itself as a matrix of one element. On computing x^T A x such that x 
is a vector with one element, the product is always positive.
# Vector world

We're going to prove that the dot product is positive definite!

## Level 4: `dot product is postive definite ` 

-/

/- Lemma
v ⬝ w = w ⬝ v for all vectors v, w ∈ ℝⁿ
-/
lemma dot_pos_def_1: ∀ {n : ℕ} (x: ℝ ^ n),  x ⬝ x ≥ 0 :=
begin 
  intro n, 
  induction n with d hd,
  { intro x, cases x, dsimp [dot_product], refl},
  {intro x, cases x with head tail, dsimp [dot_product], 
  have i: tail * tail ≥ 0, 
  {
    exact mul_self_nonneg tail, 
  }, 
  have j :x_tail ⬝ x_tail ≥ 0, 
  {
    exact hd x_tail, 
  } , 
  exact add_nonneg i j},
end

end tuple -- hide
