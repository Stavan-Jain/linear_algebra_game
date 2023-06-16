import mynat.definition -- imports the natural numbers {0,1,2,3,4,...}.
import mynat.add -- imports definition of addition on the natural numbers.
import mynat.mul -- imports definition of multiplication on the natural numbers.
namespace mynat -- hide


/- 
# Tutorial World

## Level 1: refl & rw

Let's start with the `refl` and `rw`. `refl` stands for "reflexivity". Statements can be proved by `refl` when the left hand side is *exactly equal* to the
right hand side ("definitionally equal"). And `rw` stands for "rewrite", substituting the LHS of an equality in an hypothesis h with the RHS. 

The goal of every theorem will be a mathematical statement with a `⊢` just before it.
We will use tactics to manipulate and ultimately close these goals.

Let's see how the `refl` tactic works, as a warm-up. 
-/


/- Lemma : no-side-bar
For all natural numbers $x$, we have $x = x$.
-/

lemma example1 (x: mynat) : x = x  :=
begin [nat_num_game]
  refl,



end

/-
Tactic: refl
-/

/-
Click on the word `sorry` and then delete it.
When the system finishes being busy, you'll be able to see your goal -- the objective
of this level -- in the box on the top right. 

Remember that the goal is
the thing with the weird `⊢` thing just before it. The goal in this case is `x * y + z = x * y + z`,
where `x`, `y` and `z` are some of your very own natural numbers.
That's a pretty easy goal to prove -- you can just prove it with the `refl` tactic.
Where it used to say `sorry`, write

`refl,`

For each level, the idea is to get Lean into this state: with the top right
box saying "Proof complete!" and the bottom right box empty (i.e. with no errors in).

Now we'll learn about the `rw` tactic.
-/
/-
The rewrite tactic is the way to "substitute in" the value
of a variable. If you have a hypothesis `h: A = B`, and your
goal mentions the left hand side `A` somewhere, then
the `rewrite` tactic will replace the `A` in your goal with a `B`.
This is a lemma  cannot be proved directly using `refl`. What should we do? 
-/

/- Lemma : no-side-bar
If $x$ and $y$ are natural numbers, 
and $y=x+7$, then $2y=2(x+7)$. 
-/

lemma example2 (x y : mynat) (h : y = x + 7) : 2 * y = 2 * (x + 7) :=
begin [nat_num_game]
  rw h,
  refl,
  

end

/-
Tactic: refl, rw
-/




/-

## Summary

· `refl` proves goals of the form `X = X`.

· If `h` is a proof of `X = Y`, then `rw h,` will change
all `X`s in the goal to `Y`s. Variants: `rw ← h` (changes
`Y` to `X`) and `rw h at h2` (changes `X` to `Y` in hypothesis `h2` instead
of the goal).



-/

end mynat -- hide 