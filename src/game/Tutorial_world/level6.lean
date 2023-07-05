import tactic.tauto -- useful high-powered tactic
local attribute [instance, priority 10] classical.prop_decidable -- hide

/- Axiom : not_iff_imp_false (P : Prop) :
¬ P ↔ P → false
-/
lemma not_iff_imp_false (P : Prop) : ¬ P ↔ P → false := iff.rfl -- hide
/-
# Tutorial World

## Level 6 : Contrapositive 

There is a false proposition `false`, with no proof. It is
easy to check that $\lnot Q$ is equivalent to $Q\implies {\tt false}$,
and in the natural number game we call this

`not_iff_imp_false (P : Prop) : ¬ P ↔ (P → false)`

So you can start the proof of the contrapositive below with

`repeat {rw not_iff_imp_false},`

to get rid of the two occurences of `¬`, and I'm sure you can
take it from there (note that we just added `not_iff_imp_false` to the
theorem statements in the menu on the left). At some point your goal might be to prove `false`.
At that point I guess you must be proving something by contradiction.
Or are you? 
-/

/- Lemma : no-side-bar
If $P$ and $Q$ are propositions, and $P\implies Q$, then
$\lnot Q\implies \lnot P$. 
-/
lemma contrapositive (P Q : Prop) : (P → Q) → (¬ Q → ¬ P) :=
begin
  repeat {rw not_iff_imp_false},
  intro f,
  intro h,
  intro p,
  apply h,
  apply f,
  exact p,


end

/-
## Technical note
Remember the side note on Level 2, we can use the `rw` tactic here. 
-/ 


/-


It's certainly true that $P\land(\lnot P)\implies Q$ for any propositions $P$
and $Q$, because the left hand side of the implication is false. But how do
we prove that `false` implies any proposition $Q$? A cheap way of doing it in
Lean is using the `exfalso` tactic, which changes any goal at all to `false`. 
You might think this is a step backwards, but if you have a hypothesis `h : ¬ P`
then after `rw not_iff_imp_false at h,` you can `apply h,` to make progress. 

-/



/- Lemma : no-side-bar
If $P$ and $Q$ are true/false statements, then
$$(P\land(\lnot P))\implies Q.$$
-/

lemma contra (P Q : Prop) : (P ∧ ¬ P) → Q :=
begin
  intro h,
  cases h with p np,
  rw not_iff_imp_false at np,
  exfalso,
  apply np,
  exact p,


end


/-
## Pro tip.

`¬ P` is actually `P → false` *by definition*. Try
commenting out `rw not_iff_imp_false at ...` by putting two minus signs `--`
before the `rw`. Does it still compile?
-/

/- 

## Summary

`exfalso` changes your goal to `false`. 

## Details

We know that `false` implies `P` for any proposition `P`, and so if your goal is `P`
then you should be able to `apply` `false → P` and reduce your goal to `false`. This
is what the `exfalso` tactic does. The theorem that `false → P` is called `false.elim`
so one can achieve the same effect with `apply false.elim`. 

This tactic can be used in a proof by contradiction, where the hypotheses are enough
to deduce a contradiction and the goal happens to be some random statement (possibly
a false one) which you just want to simplify to `false`.

## Further Reading (Optional):
https://leanprover.github.io/logic_and_proof/classical_reasoning.html
-/
