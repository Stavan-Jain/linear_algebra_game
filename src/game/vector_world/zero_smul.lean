import vectors.tuple -- hide
import data.real.basic --hide
import vectors.tuple.tactics --hide
import game.vector_world.level6 --hide
namespace tuple -- hide


/- 

# Vector world

## Level 8: `zero_smul` 

-/

/- Lemma

-/

lemma zero_smul : ∀ {n : ℕ} (u : ℝ ^ n), (0 : ℝ) • u = 0 :=
begin
  intro n,
  induction n with n hn,
  { intro u,
    cases u,
    simp,
    refl, },
  { intro u,
    cases u with n hea tail,
    simp,
    exact hn tail, },
end

end tuple -- hide
