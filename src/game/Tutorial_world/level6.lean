import tactic.tauto -- -- hide
local attribute [instance, priority 10] classical.prop_decidable -- hide

/- Axiom : not_iff_imp_false (P : Prop) :
¬ P ↔ P → false
-/
lemma not_iff_imp_false (P : Prop) : ¬ P ↔ P → false := iff.rfl -- hide
/-
# Tutorial World

## Level 6 : Contrapositive & the `repeat` combinator

## `repeat`

Tactic combinators build compound tactics from simpler ones, and hence simplifies proofs. 
The repeat combinator is one of the most useful combinators and will be used in the Linear Algebra Game. 

Here's how to use "Repeat": 

**repeat { tactic }**

Which is, repeatedly applies the tactic t, until t fails. The compound tactic always succeeds.
Below we have a proof for 


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

