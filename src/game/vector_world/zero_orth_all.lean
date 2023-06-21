import vectors.tuple -- hide
import vectors.orthogonal --hide
import data.real.basic
import game.vector_world.triangle_ineq --hide

namespace tuple -- hide

/- 
# Vector world

## Level 18: `Zero orthogonal` 

-/

/- Lemma
**0** is orthogonal to all vectors. 
-/

lemma zero_orth_all: ∀ {n : ℕ} (x: tuple n)
,  orthogonal tuple.zero x   :=
begin 
  intro n, 
  induction n with d ih, 
  {dsimp [orthogonal], 
  intro x, 
  cases x, 
  dsimp [tuple.zero, dot_product], refl, }, 
  {
    intro x, cases x, 
    dsimp [orthogonal, tuple.zero, dot_product],
    have i:=  ih x_tail,  dsimp [orthogonal] at i, 
    rw i, 
    simp, 
  },
end

end tuple