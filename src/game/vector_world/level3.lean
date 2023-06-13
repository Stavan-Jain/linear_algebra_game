import vectors.tuple -- hide
import data.real.basic
namespace tuple -- hide

/- 
# Vector world

We're going to prove that the dot product is commutative!  

## Level 3: `dot product is commutative ` 

-/

/- Lemma
v ⬝ w = w ⬝ v for all vectors v, w ∈ ℝⁿ
-/
lemma dot_comm: ∀ {n : ℕ} (v: tuple n) (w : tuple n),  v ⬝ w = w ⬝ v :=
begin 
  intro n, 
  induction n with d hd,
  { intros v w, cases v, cases w, dsimp [tuple.dot_product], refl,},
  { intros v w, cases v, cases w, dsimp [tuple.dot_product], 
  rw mul_comm, simp, exact hd v_tail w_tail  },
end

end tuple -- hide