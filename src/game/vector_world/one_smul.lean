import vectors.tuple -- hide
import data.real.basic
import game.vector_world.level16 --hide

namespace tuple -- hide

/- 
# Vector world

## Level 17: `Triangle Inequality` 

-/

/- Lemma
||x + y|| ≤ ||x|| + ||y||
-/

lemma one_smul: ∀ {n : ℕ} (v : tuple n)
, 1 ** v = v :=
begin 
  intro n,
  induction n with n hn,
  {intro v, cases v,
  dsimp [tuple.zero, scalar_mul, map],
  refl,},
  {intro v,
  cases v with n v₁ vₙ,
  simp,
  rw hn,
  dsimp [tuple.zero],
  refl,},
end

end tuple