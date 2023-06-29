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

set_option pp.numeral_types true  -- explain what this does

lemma smul_zero : ∀ {n : ℕ} {c : ℝ}, c • (0 : ℝ ^ n) = 0 :=
begin
  intro n,
  induction n with n hn,
  { intro c,
    refl, },
  { intro c, 
    simp,
    exact hn, },
end

end tuple -- hide
