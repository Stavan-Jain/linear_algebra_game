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
  sorry, 
end

end tuple -- hide