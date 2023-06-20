import vectors.tuple -- hide
import data.real.basic
import game.vector_world.level10 --hide

namespace tuple -- hide

/- 
# Vector world

## Level 11: `norm of neg equals norm` 

-/

/- Lemma
||-x|| = ||x||
-/


lemma norm_neg_eq_neg: ∀ {n : ℕ}  (x: tuple n)
, (tuple.neg x).norm  = x.norm   :=
begin 
  intros n x, 
  induction n with d hd generalizing x, 
  cases x, 
  simp [tuple.neg],
  cases x, 
  simp [tuple.neg], 
  dsimp [tuple.norm, norm_sq, dot_product] at *, 
  simp at *, 
  rw hd x_tail, 
end

end tuple -- hide