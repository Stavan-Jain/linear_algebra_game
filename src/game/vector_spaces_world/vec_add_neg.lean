import vectors.tuple -- hide
import data.real.basic --hide
import vectors.tuple.tactics --hide
import game.vector_spaces_world.add_zero --hide

namespace tuple -- hide


/- 


# Vector Spaces World

Strategy:
This level will give you more practice with induction!

## Level 4: `additive inverse` 

-/

/- Lemma
v + -v = 0
-/

lemma vec_add_neg : ∀ {n : ℕ} (v : ℝ ^ n), v + -v = 0 :=
begin
  intros n,
  induction n with n hn,
  { intro v,
    cases v,
    refl, },
  { intro v,
    cases v with n head tail,
    simp,
    exact hn tail, },
end

end tuple -- hide
