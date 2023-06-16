import vectors.tuple -- hide
import data.real.basic
namespace tuple -- hide

/- 
# Vector world

We're going to prove that the dot product is commutative!  

## Level 4: `dot product is postive definite ` 

-/

/- Lemma
v ⬝ w = w ⬝ v for all vectors v, w ∈ ℝⁿ
-/
lemma dot_pos_def_1: ∀ {n : ℕ} (x: tuple n),  x ⬝ x ≥ 0 :=
begin 
  intro n, 
  induction n with d hd,
  { intro x, cases x, dsimp [dot_product], refl},
  {intro x, cases x with head tail, dsimp [dot_product], 
  have i: tail * tail ≥ 0, 
  {
    exact mul_self_nonneg tail, 
  }, 
  have j :x_tail ⬝ x_tail ≥ 0, 
  {
    exact hd x_tail, 
  } , 
  exact add_nonneg i j},
end

end tuple -- hide