import vectors.tuple -- hide
import vectors.orthogonal --hide
import data.real.basic
import game.vector_world.zero_orth_all --hide

namespace tuple -- hide

/- 
# Vector world

## Level 19: `**0** is uniquely orthogonal to itself` 

-/

/- Lemma
**0** is the only vector orthogonal to itself
-/

lemma orth_self_unique_zero: ∀ {n : ℕ} (x: tuple n)
,  x ⟂ x → x = tuple.zero   :=
begin 
  intros n x,
  intro perp, 
  simp at perp,
  rw dot_pos_def_2 at perp, 
  exact perp,  
end

end tuple