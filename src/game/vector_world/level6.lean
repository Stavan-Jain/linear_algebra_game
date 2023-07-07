import vectors.tuple -- hide
import data.real.basic
import game.vector_world.level5 
namespace tuple -- hide

/- 
# Vector world

## Level 6: `Scalars pass through` 

-/

/- Lemma
(cx)·y=c (x·y) for all x, y ∈ ℝⁿ and c ∈ R

Background


In this level we'll be proving that multiplying a vector x by a scalar c and then computing the dot product of that new vector cx
with another vector y, yields the same result as multiplying the dot product of vectors x and y with scalar c.


This follows from the definition of the dot product. By multiplying vector x with scalar c, you are multiplying every one of it's elements with c.
On dotting this new vector cx with y, c can be taken out as common and multiplied with the dot product of x and y. This shows that (cx)·y = c(x·y)


Optional


The dot product of x and y, is the projection of x onto y, multiplied by the magnitude of y.
Let's first think of the definition of projection in R2. It is essentially the "shadow"
cast by one vector along another. If the projection of x on y is taken, it is easy to imagine that
as the length of x increases then the "shadow" cast on y increases and vice versa. For instance if x is doubled then the "shadow" it casts
on y is also multiplied by 2.


Now let us come back to our proof, and let's try and understand how the idea of projection might
allow us to understand it.


If vector x is multiplied by c, then its projection on y, is proportionally multiplied by c.
Also, if the projection of x on y is multiplied by c, then we attain the projection of cx on y.


This allows us to understand why multiplying a vector x by a scalar c and then computing the dot product of that new vector cx
with another vector y, yields the same result as multiplying the dot product of vectors x and y with scalar c.

-/

lemma scalar_through: ∀ {n : ℕ} (c : ℝ) (x y : ℝ ^ n), (c • x) ⬝ y = c * (x ⬝ y) :=
begin 
  intro n,
  induction n with d hd, 
  {intros c x y, 
  cases x, 
  cases y, 
  repeat {dsimp [dot_product, scalar_mul, map]}, simp,  
  },
  {
    intros c x y, 
    cases x, 
    cases y, 
    simp,
    rw mul_add,
    rw ← hd c x_tail y_tail,
    simp,
    rw mul_assoc, 
  },
end

end tuple -- hide
