import data.nat.basic  -- hide
open nat  -- hide





/-

# Tutorial World

## Level 8: The simp tactic

`Simp` is a tactic which tries to prove equalities using facts in its database.
Ideally, the database of facts would result in expressions 
being simplified into a normal form. In practice, this is often unachievable 
(normal forms may not exist, or there may not exist a collection of rewrite rules that produce them), 
but nevertheless we aim to approximate this ideal where possible. Even better, we would like the database 
of facts to be confluent, meaning the order in which the simplifier considers rewrites does not matter. Again, we aim to be close to confluent where possible.

While this system is able to prove many simple statements completely automatically, proving all simple statements is not part of its job description, as disappointing as that might be.

Here is an example (using mathlib).


## Details

The `simp` tactic does basic automation. `Simp` is able
to solve all equalities whose proofs involve a tedious number
of rewrites of `add_assoc` and `add_comm`, and by
level 9 of Multiplication World the same is true of `mul_assoc` and `mul_comm`.


### Example:
If our goal is this:
```
⊢ a + b + c + d + e = c + (b + e + a) + d
```
-/


/- Lemma : no-side-bar
For all natural numbers $a,b,c$, we have $a * b * c = c * b * a$.
-/

lemma commuting (a b c : ℕ) : a * b * c = c * b * a  :=
begin 
  simp,



end

/-

## The `simpa` tactics
`simpa` is a "finishing" tactic modification of simp which has two forms.

`simpa [rules, ...] using e` will simplify the goal and the type of e using rules, then try to close the goal using e.

Simplifying the type of e makes it more likely to match the goal (which has also been simplified). This construction also tends to be more robust under changes to the simp lemma set.

`simpa [rules, ...]` will simplify the goal and the type of a hypothesis this if present in the context, then try to close the goal using the assumption tactic.

If `simp` cannot close a goal, try `simpa` instead. 
-/

end mynat -- hide 