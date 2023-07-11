
/-
# Tutorial World 
## Level 3: The `split`, `cases` tactics

In this level we will learn `split` and `cases`, with the notion of Union and Intersection.   

## split: 

The logical symbol `∧` means "and". If $P$ and $Q$ are propositions, then
$P\land Q$ is the proposition "$P$ and $Q$". If your *goal* is `P ∧ Q` then
you can make progress with the `split` tactic, which turns one goal `⊢ P ∧ Q`
into two goals, namely `⊢ P` and `⊢ Q`. In the level below, after a `split`,
you will be able to finish off the goals with the `exact` or `apply` tactic.
-/

/- Lemma : no-side-bar
If $P$ and $Q$ are true, then $P\land Q$ is true.
-/
example (P Q : Prop) (p : P) (q : Q) : P ∧ Q :=
begin
  split,
  exact p,
  exact q,


end 

/-
### Details

If `P Q : Prop` and the goal is `⊢ P ∧ Q`, then `split` will change it into
two goals, namely `⊢ P` and `⊢ Q`. 

If `P Q : Prop` and the goal is `⊢ P ↔ Q`, then `split` will change it into
two goals, namely `⊢ P → Q` and `⊢ Q → P`.  

-/ 


/- 
## cases: 

If `P ∧ Q` is in the goal, then we can make progress with `split`.
But what if `P ∧ Q` is a hypothesis? In this case, the `cases` tactic will enable
us to extract proofs of `P` and `Q` from this hypothesis.

The lemma below asks us to prove `P ∧ Q → Q ∧ P`, that is,
symmetry of the "and" relation. The obvious first move is

`intro h,`

because the goal is an implication and this tactic is guaranteed
to make progress. Now `h : P ∧ Q` is a hypothesis, and

`cases h with p q,`

will change `h`, the proof of `P ∧ Q`, into two proofs `p : P`
and `q : Q`. From there, `split` and `exact` will get you home. Below is a demonstration of how
cases works.

-/


/- Lemma
If $P$ and $Q$ are true/false statements, then $P\land Q\implies Q\land P$. 
-/

lemma and_symm (P Q : Prop) : P ∧ Q → Q ∧ P :=
begin
  intro h,
  cases h with p q,
  split,
  apply q,
  apply p,


end 


/- 


### Details

How does one prove `P ∧ Q`? The way to do it is to prove `P` and to
prove `Q`. There are hence two ingredients which go into a proof of
`P ∧ Q`, and the `cases` tactic extracts them. 

More precisely, if the local context contains
```
h : P ∧ Q`
```

then after the tactic `cases h with p q,` the local context will
change to
```
p : P,
q : Q
```
and `h` will disappear. 

Similarly `h : P ↔ Q` is proved by proving `P → Q` and `Q → P`,
and `cases h with hpq hqp` will delete our assumption `h` and
replace it with
```
hpq : P → Q,
hqp : Q → P
```

Be warned though -- `rw h` works with `h : P ↔ Q` (`rw` works with
`=` and `↔`), whereas you cannot rewrite with an implication.

`cases` also works with hypotheses of the form `P ∨ Q` and even
with `n : ℕ`. Here the situation is different however. 
To prove `P ∨ Q` you need to give either a proof of `P` *or* a proof
of `Q`, so if `h : P ∨ Q` then `cases h with p q` will change one goal
into two, one with `p : P` and the other with `q : Q`. Similarly, each
natural is either `0` or `succ(d)` for `d` another natural, so if
`n : ℕ` then `cases n with d` also turns one goal into two,
one with `n = 0` and the other with `d : ℕ` and `n = succ(d)`.
-/

/-
## Summary:
· The `split` tactic deals with the `and` logic. If the goal is `P ∧ Q` or `P ↔ Q` then `split` will break it into two goals.

· The `cases` tactic deals with the `or` logic. If the hypothesis is `h: P ∧ Q`, then `cases h with p q` will discuss the two cases, i.e.,
break the hypothesis into `p: P` and `q: Q`, namely, two cases.
-/ 
