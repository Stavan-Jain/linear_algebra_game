import vectors.tuple -- hide
import data.real.basic --hide
import game.vector_world.lin_comb2 --hide
namespace tuple -- hide

/- 


# Vector world

Background:
Before we go on to our proof, let's try to develop some intution for why the dot product is commutative. 
The dot product allows us to gauge how much one vector is going in the direction of another vector i.e their degree of alignment. 
The amount that vector 1 goes in the direction of vector 2 must be the same as the amount that vector 2 goes in the direction of vector 1. 

Next let us learn about an important proof technique called mathematical induction. If you've gone through 
the natural number game you may be familiar with it. Mathematical induction is a powerful method of 
mathematical proof used to establish the truth of an infinite sequence of statements. It has three components: 
a base case, an inductive hypothesis, and an inductive step. First we prove that a statement is true for an 
initial value of base case (usually 0 or one.) Then in the inductive hypothesis, it is taken to be true for 
some value k, using which it is used to prove that it is true for k+1 through the inductive step. Hence it is proved. Induction will come in handy
in this proof. 

Strategy:
1. Begin this proof as follows: 

"intros n v w," 

This allows you to define Rⁿ and vectors v,w ∈ Rⁿ 

2. Next, using induction we will prove firstly that the dot product is commutative for the zero vector, and assume that 
it is true for some vector of length n. Using this we will prove that it is true for a vector of length n+1.

Induction is initiated in Lean in the following manner (n and hn are variables): 

"induction n with hn"

3. The "cases" tactic allows you to deconstruct an inductive type. When applied to a vector of length n, it 
breaks into a two tuple, with first element or "head" ∈ R and second element or "tail" of length n-1. 

4. The "simp" tactic simplifies all hypotheses and goals. Essentially, it breaks them down to their basis definitions. 

Hint:
Think about how "cases" can help you prove that if the dot product is commutative for a vector of length n, it 
must be true for a vector of length n+1. 

If you see something like this: cons v_head v_tail ⬝ cons w_head w_tail = cons w_head w_tail ⬝ cons v_head v_tail
try applying "simp" and see what happens.

We're going to prove that the dot product is commutative!  

## Level 1: `dot product is commutative ` 

-/

/- Lemma
v ⬝ w = w ⬝ v for all vectors v, w ∈ ℝⁿ
-/
lemma dot_comm : ∀ {n : ℕ} (v : ℝ ^ n) (w : ℝ ^ n),  v ⬝ w = w ⬝ v :=
begin 
  intros n v w,
  induction n with d hd,
  { cases v, cases w,
    simp, },
  { cases v, cases w, 
    simp, 
    rw mul_comm,
    simp,
    exact hd v_tail w_tail, },
end

end tuple -- hide
