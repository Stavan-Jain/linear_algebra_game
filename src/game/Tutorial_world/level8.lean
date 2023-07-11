import data.nat.basic  -- hide
open nat  -- hide

/-
# Tutorial World 
## Level 8: Induction

NB: the use of Induction later in this game can sometimes be counter-intuitive, 
regarding a normal (natural) way of proving Linear Algebra theorems. 
Because of the formalized and computational nature of Lean, these are inevitable, 
yet we will provide enough hints when such counter-intuitive proofs occur.

## Details

If you have a natural number `n : ℕ` in your context
(above the `⊢`) then `induction n with d hd` turns your
goal into two goals, a base case with `n = 0` and
an inductive step where `hd` is a proof of the `n = d`
case and your goal is the `n = succ(d)` case.



## Data:
By Piano's Axioms, we have:
  * a type called natural numbers (`ℕ`). 
  * a term `0 : ℕ`, interpreted as the number zero.
  * a function `succ : ℕ → ℕ`, with `succ n` interpreted as "the number after `n`".
  * Usual numerical notation 0,1,2 etc (although 2 onwards will be of no use to us until much later ;-) ).
  * Addition (with notation `a + b`).

## Theorems:

  * `add_zero (a : ℕ) : a + 0 = a`. Use with `rw add_zero`.
  * `add_succ (a b : ℕ) : a + succ(b) = succ(a + b)`. Use with `rw add_succ`.
  * The principle of mathematical induction. Use with `induction` (see below)
  

## Tactics:

  * `refl` :  proves goals of the form `X = X`
  * `rw h` : if h is a proof of `A = B`, changes all A's in the goal to B's.
  * `induction n with d hd` : we're going to learn this right now.



OK so let's see induction in action. We're going to prove

  `zero_add (n : ℕ) : 0 + n = n`. 

After we start the induction process, we see that we now have *two goals*! The
induction tactic has generated for us a base case with `n = 0` (the goal at the top)
and an inductive step (the goal underneath). The golden rule: **Tactics operate on the first goal** --
the goal at the top. So let's just worry about that top goal now, the base case `⊢ 0 + 0 = 0`.

Remember that `add_zero` is the proof of `x + 0 = x`
(for any $x$) so we can try

`rw add_zero,`

 What do you think the goal will
change to? Remember to just keep
focussing on the top goal, ignore the other one for now, it's not changing
and we're not working on it. You should be able to solve the top goal yourself
now with `refl`.

When you solved this base case goal, we are now be back down
to one goal -- the inductive step. Take a look at the
text below the lemma to see an explanation of this goal.
-/

/- Lemma
For all natural numbers $n$, we have
$$0 + n = n.$$
-/
lemma zero_adding (n : ℕ) : 0 + n = n :=
begin
  induction n with d hd,
  rw add_zero,
  rw add_succ,
  rw hd,

end

/-

## Summary

if `n : ℕ` is in our assumptions, then `induction n with d hd`
attempts to prove the goal by induction on `n`, with the inductive
assumption in the `succ` case being `hd`.

-/
