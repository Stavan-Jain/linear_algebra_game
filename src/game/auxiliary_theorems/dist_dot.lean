import game.auxiliary_theorems.sub_eq_add_neg --hide
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


## Level 2: `Distributive Property` 

-/

/- Lemma
x ⬝ (y + z) = (x ⬝ y) + (x ⬝ z)


-/

lemma dist_dot: ∀ {n : ℕ} (x y z : ℝ ^ n), (y + z) ⬝ x = (y ⬝ x) + (z ⬝ x) :=
begin 
  intros n x y z,
  induction n with d hd, 
  { casesm* (ℝ ^ 0),
    simp, },
  { cases x with _ x₁ xₙ,
    cases y with _ y₁ yₙ,
    cases z with _ z₁ zₙ,
    simp,
    calc (y₁ + z₁) * x₁ + (yₙ + zₙ) ⬝ xₙ = y₁ * x₁ + z₁ * x₁ + (yₙ + zₙ) ⬝ xₙ : by ring_nf
      ... =  y₁ * x₁ + z₁ * x₁ + (yₙ ⬝ xₙ + zₙ ⬝ xₙ) : by rw hd xₙ yₙ zₙ
      ... = y₁ * x₁ + yₙ ⬝ xₙ + (z₁ * x₁ + zₙ ⬝ xₙ) : by ring_nf, },
end

end tuple -- hide
