import vectors.tuple -- hide
import data.real.basic --hide
import vectors.tuple.tactics --hide
import game.vector_spaces_world.vec_comm --hide
namespace tuple -- hide


/- 

# Vector Spaces World

Background:
Here we will get introduced to the concept of mathematical induction. If you've gone through the
natural number game you may be familiar with it. Mathematical induction is a powerful method to
prove statements about all natural numbers. It has three components: a base case, an inductive
hypothesis, and an inductive step. First we prove that our claim is true for an initial value of
base case (usually 0 or 1); then, in the inductive step, we prove that it is true for some number k
greater than the base case assuming that it is true for k-1. This assumption is called the
"inductive hypothesis", or `ih` for short. It can help to think of induction as a domino effect,
where each number implies the next.

Strategy:
In Lean induction is initiated in the following manner (`k` is a variable and `ih` is the induction
hypothesis):

```
intro n
induction n with k ih
```

This gives two goals to prove,

1. that a statement is true for the base case (here, 0)
2. that if the statement is true for `k` then it is true for `k+1`

Induction on vectors in ℝⁿ is done by showing that if a statement is true for the vector of zero
length, and is assumed to be true for a vector of length `k` then it can be proved for a vector of
length `k+1`.

Hint: `cases v with n head tail` will break a vector of length `n+1` into two `head` and `tail`,
with `head` being the first element, and `tail` being the `n` other elements. You should also try
`cases v` when `v` has length `0`.

## Level 3: `add_zero`

-/

/- Lemma

-/

lemma add_zero : ∀ {n : ℕ} (u : ℝ ^ n), u + 0 = u :=
begin
  intro n,
  induction n with n hn,
  { intro v,
    cases v,
    refl, },
  { intro v,
    cases v with n head tail,
    simp,
    exact hn tail, },
end

end tuple -- hide
