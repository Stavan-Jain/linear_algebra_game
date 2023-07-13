import vectors.tuple -- hide
import data.real.basic
import game.dot_prod_world.dot_comm --hide
namespace tuple -- hide

/- 
# Vector world

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


## Level 4: `Distributive Property` 

-/

/- Lemma
x ⬝ (y + z) = (x ⬝ y) + (x ⬝ z)


-/

lemma dot_dist: ∀ {n : ℕ} (x y z : ℝ ^ n), x ⬝ (y + z) = (x ⬝ y) + (x ⬝ z) :=
begin 
  intros n x y z,
  induction n with d hd, 
  { casesm* (ℝ ^ 0),
    simp, },
  { cases x with _ x₁ xₙ,
    cases y with _ y₁ yₙ,
    cases z with _ z₁ zₙ,
    simp,
    calc x₁ * (y₁ + z₁) + xₙ ⬝ (yₙ + zₙ) = x₁ * y₁ + x₁ * z₁ + xₙ ⬝ (yₙ + zₙ) : by ring_nf
      ... = x₁ * y₁ + x₁ * z₁ + (xₙ ⬝ yₙ + xₙ ⬝ zₙ) : by rw hd xₙ yₙ zₙ
      ... = x₁ * y₁ + xₙ ⬝ yₙ + (x₁ * z₁ + xₙ ⬝ zₙ) : by ring_nf, },
end

end tuple -- hide
