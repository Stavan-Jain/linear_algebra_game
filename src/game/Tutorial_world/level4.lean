import data.nat.basic -- hide
import tactic.ring -- hide
open nat -- hide


/-
# Tutorial World 
## Level 4: The `Use` and `Ring` tactics
-/


/-
## Use:

`use` is a tactic which works on goals of the form `⊢ ∃ c, P(c)` where
`P(c)` is some proposition which depends on `c`. With a goal of this
form, `use 0` will turn the goal into `⊢ P(0)`. `use x + y` (assuming
`x` and `y` are natural numbers in your local context) will turn
the goal into `P(x + y)` and so on.
-/

/- 
 If `a` and `b` are naturals, `a ≤ b` is *defined* to mean

`∃ (c : ℕ), b = a + c`. 

So, we have the axiom, le_iff_exists_add (a b : ℕ)
  a ≤ b ↔ ∃ (c : ℕ), b = a + c

In words, $a\le b$
if and only if there exists a natural $c$ such that $b=a+c$. 

If you really want to change an `a ≤ b` to `∃ c, b = a + c` then
you can do so with `rw le_iff_exists_add`:

But because `a ≤ b` is *defined as* `∃ (c : ℕ), b = a + c`, you
do not need to `rw le_iff_exists_add`, you can just pretend when you see `a ≤ b`
that it says `∃ (c : ℕ), b = a + c`. You will see a concrete
example of this below.

A new construction like `∃` means that we need to learn how to manipulate it.
There are two situations. Firstly we need to know how to solve a goal
of the form `⊢ ∃ c, ...`, and secondly we need to know how to use a hypothesis
of the form `∃ c, ...`. 



The goal below is to prove $x\le 1+x$ for any natural number $x$. 
First let's turn the goal explicitly into an existence problem with

`rw le_iff_exists_add,`

and now the goal has become `∃ c : mynat, 1 + x = x + c`. Clearly
this statement is true, and the proof is that $c=1$ will work (we also
need the fact that addition is commutative, but we proved that a long
time ago). How do we make progress with this goal?

The `use` tactic can be used on goals of the form `∃ c, ...`. The idea
is that we choose which natural number we want to use, and then we use it.
So try

`use 1,`

and now the goal becomes `⊢ 1 + x = x + 1`. You can solve this by
`exact add_comm 1 x`, or if you are lazy you can just use the `ring` tactic,
which is a powerful AI which will solve any equality in algebra which can
be proved using the standard rules of addition and multiplication. Now
look at your proof. We're going to remove a line.


## Ring:
When dealing with equalities with basic algebraic manipulation, using the tactics we've described so far
and relying on the axoims of addition and multiplication can be tedious sometimes. 

Here, we introduce the `ring` tactic, which can serve to reduce the tedium by closing 
some goals. 

The `ring` tactic proves identities in commutative rings such as (x+y)^2=x^2+2*x*y+y^2. 
It works on concrete rings such as ℝ and abstract rings, and will also prove some results in “semirings” such as ℕ.
Note that ring does not and cannot look at hypotheses.

Ring is a “finishing tactic”; this means that it should only be used to close goals. 
If ring does not close a goal it will issue a warning that you should use the related tactic ring_nf.



## Important

An important time-saver here is to note that because `a ≤ b` is *defined*
as `∃ c : ℕ, b = a + c`, you *do not need to write* `rw le_iff_exists_add`.
The `use` tactic will work directly on a goal of the form `a ≤ b`. Just
use the difference `b - a` (note that we have not defined subtraction so
this does not formally make sense, but you can do the calculation in your head).
If you have written `rw le_iff_exists_add` below, then just put two dashes `--`
before it and comment it out. See that the proof still compiles.
-/

/- Lemma : no-side-bar
If $x$ is a natural number, then $x\le 1+x$.
-/
lemma one_add_le_self (x : ℕ) : x ≤ 1 + x :=
begin
  rw le_iff_exists_add,
  use 1,
  ring,


end 


/- 
## Summary

· `use` works on the goal. If your goal is `⊢ ∃ c : ℕ, 1 + x = x + c`
then `use 1` will turn the goal into `⊢ 1 + x = x + 1`. 

· `ring` closes goals when goals can be proved by the ring algebra. 

-/ 

