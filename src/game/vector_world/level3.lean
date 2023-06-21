import vectors.tuple -- hide
import data.real.basic 
import game.vector_world.level2 --hide
namespace tuple -- hide

/- 

Before we go on to our proof, let's try to develop some intution for why the dot product is commutative. 
The dot product allows us to gauge how much one vector is going in the direction of another vector i.e their degree of alignment. 
The amount that vector 1 goes in the direction of vector 2 must be the same as the amount that vector 2 goes in the direction of vector 1. 

# Vector world

We're going to prove that the dot product is commutative!  

## Level 3: `dot product is commutative ` 

-/

/- Lemma
v ⬝ w = w ⬝ v for all vectors v, w ∈ ℝⁿ
-/
lemma dot_comm: ∀ {n : ℕ} (v: tuple n) (w : tuple n),  v ⬝ w = w ⬝ v :=
begin 
  intros n,
  induction n with d hd,
  { intros v w, cases v, cases w, dsimp [tuple.dot_product], refl,},
  { intros v w, cases v, cases w, dsimp [tuple.dot_product], 
  rw mul_comm, simp, exact hd v_tail w_tail  },
end

end tuple -- hide