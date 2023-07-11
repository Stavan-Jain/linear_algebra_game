import algebra.group.defs  -- hide
open nat  -- hide





/-

# Tutorial World

## Level 9: The simp tactic

`simp` is a tactic which tries to prove equalities using facts in its database.
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
of rewrites of other tactics which have already been introduced.

The following lemma is an example. (If you haven't seen the following definition, don't worry! The lemma we're proving is simple!)

We defined an algebraic structure (a set G equipped by a binary operation denoted by *) called a "group" by the following axioms: 

Associativity: for elements a, b, and c in the group G, $a * (b * c) = (a * b) * c$.
Identity: there's the identity element 1 such that $1 * g = g * 1 = g$ for all elements g in G. 
Inverse: for each element g in G, there exists an inverse for it, $g⁻¹$, such that they "annihilates": $g⁻¹ * g = g * g⁻¹ = 1$. 
-/

/- 
As we've already defined such axoims and properties, including:
[mul_right_inv]: a * a⁻¹ ==> 1
[mul_one]: 1 * 1 ==> 1
[one_mul]: 1 * b ==> b
[mul_inv_cancel_right]: b * c * c⁻¹ ==> b
[eq_self_iff_true]: b = b ==> true

Solely using `simp` will close the goal. 
-/

/- Lemma : no-side-bar 
for three arbitrary elements a, b and c in an arbitrary group G with the identity 1, we always have $a * a⁻¹ * 1 * b = b * c * c⁻¹$, where $*$ denotes the group operation. 
-/

variables (G : Type) [group G] (a b c : G) 

lemma fancy_algebraic_manipulation : a * a⁻¹ * 1 * b = b * c * c⁻¹ :=
begin
  simp
end

/-

## The `simpa` tactics
`simpa` is a "finishing" tactic modification of simp which has two forms.

`simpa [rules, ...] using e` will simplify the goal and the type of e using rules, then try to close the goal using e.

Simplifying the type of e makes it more likely to match the goal (which has also been simplified). This construction also tends to be more robust under changes to the simp lemma set.

`simpa [rules, ...]` will simplify the goal and the type of a hypothesis this if present in the context, then try to close the goal using the assumption tactic.

If `simp` cannot close a goal, try `simpa` instead. 
-/

/-
### p.s. Try using `simp` on level 1, 4, and 8! 
-/


