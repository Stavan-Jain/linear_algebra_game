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

lemma orth_self_unique_zero: ∀ {n : ℕ} (x: ℝ ^ n)
,  x ⟂ x → x = 0   :=
begin 
  intros n x perp,
  simp at perp,
  rwa dot_pos_def_2 at perp,
end

end tuple
