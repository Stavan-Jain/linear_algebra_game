import data.nat.basic  -- hide
open nat  -- hide

/-

# Tutorial World

## Level 10: The `Repeat` Combinator 

-/ 

/-
Tactic combinators build compound tactics from simpler ones, and hence simplifies proofs. 
The repeat combinator is one of the most useful combinators and will be used in the Linear Algebra Game. 

Here's how to use "Repeat": 

**repeat { tactic }**

Which is, repeatedly applies the tactic t, until t fails. The compound tactic always succeeds.
Below we have a proof for 
-/ 


example : ∀ a b c : ℕ, a = b → a = c → c = b :=
begin
  intros,
  transitivity,
  symmetry,
  assumption,
  assumption
end

/- Lemma : no-side-bar
Simplify the proof using *repeat*:
-/

lemma ∀ a b c : ℕ, a = b → a = c → c = b :=
begin 
  intros,
  transitivity,
  symmetry,
  repeat { assumption }



end



