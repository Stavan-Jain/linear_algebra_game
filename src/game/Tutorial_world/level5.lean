import data.nat.basic -- hide
import tactic.linarith -- hide
open nat -- hide


/-
# Tutorial World 

## Level 5: The `linarith` tactics

Similar to the `ring` tactic, linarith (linear arithmatic）also aims to simplify the process of proofs.
Specifically, it solves certain kinds of linear equalities and inequalities.
Unlike the ring tactic, linarith uses hypotheses in the tactic state.

If you have a bunch of hypotheses like h1 : a < b, h2 : b <= c, h3 : c = d and a goal of a < d, 
then linarith will solve it. Linarith knows how to combine linear relations: it knows a ton of results about how to put inequalities together and will close such goals. 

-/

/- Lemma : no-side-bar
If $x y a b$ are natural numbers, and if $x < y$, $a < b$, then $ x + a <  y + b$.
-/
lemma linarith (x y a b : ℕ) (h1 : x < y) (h2: a < b) : x + a < y + b :=
begin
  linarith,

end
