import data.nat.basic  -- hide
open nat -- hide
 

/- 
# Tutorial World
 
## Level 1: The rewrite (rw) tactic

The rewrite tactic is the way to "substitute in" the value
of a variable. If you have a hypothesis `h: A = B`, and your
goal mentions the left hand side `A` somewhere, then
the `rewrite` tactic will replace the `A` in your goal with a `B`. If you want to substitute `B` 
with `A`, then a variant of the rewrite tactic, `rw <-` (type \l), will close the goal. 

This is a lemma cannot be proved directly using `refl`. What should we do? 
-/

/- Lemma : no-side-bar
If $x$ and $y$ are natural numbers, 
and $y=x+7$, then $2y=2(x+7)$. 
-/

lemma Rewrite (x y : ℕ) (h : y = x + 7) : 2 * y = 2 * (x + 7) :=
begin 
  rw h, 


end




/-

## Summary

· If `h` is a proof of `X = Y`, then `rw h,` will change
all `X`s in the goal to `Y`s. 

· Variants: `rw ← h` (changes
`Y` to `X`) and `rw h at h2` (changes `X` to `Y` in hypothesis `h2` instead
of the goal).

-/