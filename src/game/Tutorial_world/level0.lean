import data.nat.basic  -- hide
open nat -- hide
 

/- 
# Tutorial World
Lean is a theorem prover and programming language launched by Leonardo de Moura at Microsoft Research in 2013.

This world is made for students who have zero or little experience with
Lean, aiming to provide a quick intro to Lean (Lean 3) and 
the tactics you will need to kickstart the Linear Algebra Game. If you've already played the Natural number game
or feel comfortable with Lean, then you can probably skip to the next world. 

References: Kevin Buzzard's Natural Number Game (https://www.ma.imperial.ac.uk/~buzzard/xena/natural_number_game/).

For additional resources on learning fundamentals of Lean, visit the site above. 

## Level 0: The refl tactic
Let's start with two tactics: `refl` and `rw`. `refl` stands for "reflexivity". Statements can be proved by `refl` when the left hand side is excatly the same as the
right hand side ("definitionally equal"). And `rw` stands for "rewrite", substituting the LHS of an equality in an hypothesis h with the RHS. 

For every theorem, your goal will be the mathematical statement with a `⊢` just before it.
We will use tactics to manipulate and ultimately close these goals.

Let's see how the `refl` tactic works, as a warm-up. 

The first step for every level in this game is to click on the word `sorry` and then delete it (it's just a filler word for syntax purposes).
For this lemma, the `refl` tactic will close the goal, as both side are *exactly* the same. 
-/



/- Lemma : no-side-bar
For all natural numbers $x$, we have $x = x$.
-/

lemma demo (x : ℕ) : x = x :=
begin 
  refl,



end

/-
 
For each level, the idea is to get Lean into this state: with the top right
box saying "Proof complete!" and the bottom right box empty (i.e. with no errors in).
-/

/-

## Summary

· `refl` closes goals of the form `X = X`.

-/
