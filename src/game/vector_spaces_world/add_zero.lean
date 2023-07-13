import vectors.tuple -- hide
import data.real.basic --hide
import vectors.tuple.tactics --hide
import game.vector_spaces_world.vec_comm --hide
namespace tuple -- hide


/- 

# Vector Spaces World

Background:
Here we will get introduced to the concept of mathematical induction. If you've gone through 
the natural number game you may be familiar with it. Mathematical induction is a powerful method of 
mathematical proof used to establish the truth of an infinite sequence of statements. It has three components: 
a base case, an inductive hypothesis, and an inductive step. First we prove that a statement is true for an 
initial value of base case (usually 0 or one.) Then in the inductive hypothesis, it is taken to be true for 
some value k, using which it is used to prove that it is true for k+1 through the inductive step. Hence it is proved. 

Strategy:
In Lean induction is initiated in the following manner (d and hd here are variable): 

intro d
induction d with d hd

This gives two goals to prove, 1) that a statement is true for the base case (here, 0), 2) that if the statement is true for k then it is true for k+1. 

Induction on vectors is done by showing that if a statement is true for the zero vector, and is assumed to be true for a vector of length n
then it can be proved for a vector of length n+1. 

Begin this proof as such:

intro n,
induction n with n hn

Hint:

Remember, 

"cases v with n head tail" will break a vector of length n+1 into a 2-tuple with first element being of length 1, and second element being a tuple of length n. 

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
