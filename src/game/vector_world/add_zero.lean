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

lemma add_zero {n : ℕ} : ∀ (v : tuple n), v + 0 = v :=
begin 
  induction n with n hn,
  { intro v, cases v,
    refl, },
  { intro v,
    cases v with n head tail,
    simp,
    exact hn tail, },
end

end tuple