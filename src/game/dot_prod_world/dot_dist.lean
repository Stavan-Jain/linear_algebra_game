import vectors.tuple -- hide
import data.real.basic
import game.dot_prod_world.dot_pos_def_2--hide
namespace tuple -- hide

/- 
# Vector world

## Level 4: `Distributive Property` 

-/

/- Lemma
x ⬝ (y + z) = (x ⬝ y) + (x ⬝ z)

Before proving the distributivity of the dot product algebraically, let’s attempt to understand it geometrically in R2. 
For convenience, let us rewrite x ⬝ (y + z) as (y+z) ⬝ x, (x.y) as (y.x), and (x.z) as (z.x). 
(We have already shown that the dot product is commutative.) Now let’s return to the idea of projections and shadows. 

The magnitude of the projection of y on x is y.x/mag(x). The magnitude of the projection of z on x is z.x/mag(x).
Now let us imagine the projection of y+z on x. On visualizing it’s easy to see that the length of the shadow 
cast by y+z on x is the sum of the shadows cast by y and z. If the projection of (y+z) on x is equal to the sum of the projections 
of y on x and z on x then it must be that the dot product of y+z and x is equal to y.x + z.x, and hence that:

x ⬝ (y + z) = (x ⬝ y) + (x ⬝ z).

Strategy:  

Let’s take a minute to get introduced to cases_matching p. This tactic applies cases to a hypothesis h if it type matches the pattern of p. 
For instance, the following tactic destructs all conjunctions and disjunctions in the current goal.

-/

lemma dot_dist: ∀ {n : ℕ} (x: ℝ ^ n) (y : ℝ ^ n) (z : ℝ ^ n)
,  x ⬝ (y + z) = (x ⬝ y) + (x ⬝ z) :=
begin 
  intro n,
  induction n with d hd, 
  {intros x y z, 
  casesm* (ℝ ^ 0),
  dsimp [dot_product],
  rw add_zero, 
  },
  {
    intros x y z, 
    casesm* (ℝ ^ d.succ),
    simp [tuple.dot_product],
    have i : x_head * y_head + x_tail ⬝ y_tail + (x_head * z_head + x_tail ⬝ z_tail)
    = x_tail ⬝ y_tail + x_tail ⬝ z_tail +  x_head * y_head + x_head * z_head , 
    {
      linarith, 
    }, 
    rw i, 
    rw ← hd x_tail y_tail z_tail,  
    linarith, 
  },
end

end tuple -- hide
