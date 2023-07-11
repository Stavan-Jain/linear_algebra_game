import data.nat.basic  -- hide
open nat -- hide
 

/- 
# Tutorial World
Lean is a theorem prover and programming language launched by Leonardo de Moura at Microsoft Research in 2013.

This world is made for students who have zero or little experiences with
Lean, aiming to provide a quick intro to Lean (Lean 3) and 
the tactics you will need to kickstart the Linear Algebra Game. 

References: Kevin Buzzard's Natural Number Game (https://www.ma.imperial.ac.uk/~buzzard/xena/natural_number_game/).

For additional resources on learning fundamentals of Lean, visit the site above. 

## Level 1: The refl & rw tactics
Let's start with two tactics: `refl` and `rw`. `refl` stands for "reflexivity". Statements can be proved by `refl` when the left hand side is excatly the same as the
right hand side ("definitionally equal"). And `rw` stands for "rewrite", substituting the LHS of an equality in an hypothesis h with the RHS. 

For every theorem, your goal will be the mathematical statement with a `⊢` just before it.
We will use tactics to manipulate and ultimately close these goals.

Let's see how the `refl` tactic works, as a warm-up. If we have the lemma below: 
-/



/- Lemma : no-side-bar
For all natural numbers $x$, we have $x = x$.
-/

lemma example1 (x: ℕ) : x = x  :=
begin 
  refl,



end

/-
`Refl` here will close the goal. 

Now we'll learn about the `rw` tactic.

The rewrite tactic is the way to "substitute in" the value
of a variable. If you have a hypothesis `h: A = B`, and your
goal mentions the left hand side `A` somewhere, then
the `rewrite` tactic will replace the `A` in your goal with a `B`. If you want to substitude `B` 
with `A`, then a variant of the rewrite tactic, `rw <-`, would close the goal. 

The first step for every level in this game is to click on the word `sorry` and then delete it (it's just a filler word for syntax purposes).
For this lemma, the `refl` tactic will close the goal, as both side are *exactly* the same. 

For each level, the idea is to get Lean into this state: with the top right
box saying "Proof complete!" and the bottom right box empty (i.e. with no errors in).
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

· `refl` closes goals of the form `X = X`.

· If `h` is a proof of `X = Y`, then `rw h,` will change
all `X`s in the goal to `Y`s. 

· Variants: `rw ← h` (changes
`Y` to `X`) and `rw h at h2` (changes `X` to `Y` in hypothesis `h2` instead
of the goal).



-/
