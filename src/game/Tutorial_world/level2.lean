/-
# Tutorial World

## Level 2: The `intro`, `exact` and `apply` tactics

## Intro:

`Intro` is a fundamental tactic dealing with propositions in Lean, and here you'll learn how to use it.

If we have a true/false statement $P$, let's prove a intuitive result: $P\implies P$. 

Constructing a term of type `P → P` in this case amounts to proving that $P\implies P$,
and computer scientists think of this as coming up with a function 
which sends proofs of $P$ to proofs of $P$.

To define an implication $P\implies Q$ we need to choose an arbitrary
proof $p : P$ of $P$ and then construct a proof of $Q$, which is
"let's assume $P$ is true". In Lean, this is `intro p`, i.e., 
"let's assume we have a proof of $P$" (note that this is the *lowercase* p).

### Template: 

If your goal is to prove anything in the form of `P → Q` (i.e. that $P\implies Q$),
then `intro p`, meaning "assume $p$ is a proof of $P$", will make progress.

To solve the goal below, you have to come up with a function from
`P` (thought of as the set of proofs of $P$!) to itself. Start with

`intro p,`

(i.e. "let $p$ be a proof of $P$") and note that our
local context now looks like this:

```
P : Prop,
p : P
⊢ P
```

Our job now is to construct a proof of $P$. 

## Exact: 
`Exact` is another fundamental tactic dealing with propositions. It signals that the expression given should fill the goal exactly. Suppose `h: P → Q` is a hypothesis 
that $P\implies Q$, and `p: P` is a proof of `P`. Then `exact h(p)` will close the goal `⊢Q` (if we have a proof for P, namely `p`, then h(p) is a proof for Q). 
Yet, for most of the cases, you can use the `apply` tactic, will be introduced later, to substitute `exact`. 

Continue what we left there, we need to construct of proof for $P$. But, by definition, $p$ is a proof of $P$. 

So, `exact p,` will close the goal. 

Note that `exact P` will not work -- don't
confuse a true/false statement (which could be false!) with a proof.
We will stick with the convention of capital letters for propositions
and small letters for proofs.

### Side Note: 

All of that rewriting you did with `rw` previously
was rewriting hypothesis of the form `h : X = Y`, but
you can also `rw h` if `h : P ↔ Q`. 

-/ 


/- Lemma : no-side-bar
If $P$ is a proposition then $P\implies P$.
-/
lemma imp_self (P : Prop) : P → P :=
begin
  intro p,
  exact p,

end

/-
## Apply 
`Apply` is the last tactic we have for this level. The apply tactic tries to match the current goal against the conclusion of the type of term. 
The argument term should be a term well-formed in the local context of the main goal. In other words, `apply h` will simplify the goal by applying the 
hypothesis h (a proof) on it. 

(try using `apply p` to close the lemma!)
-/

/-

## Summary

· `exact p` means the proof p fill the goal exactly.

· `intro p` means let's assume we have a proof of $P$. 

· `apply p` means to use the implication p we're assuiming. 


-/
