import vectors.tuple -- hide
import data.real.basic
import game.vector_world.level5 
namespace tuple -- hide

/- 
# Vector world

## Level 6: `Scalars pass through` 

-/

/- Lemma
(cx)·y=c (x·y) for all x, y ∈ ℝⁿ and c ∈ R
-/

lemma scalar_comm : ∀ {n : ℕ} (c d : ℝ) (v : ℝ ^ n), c • d • v = d • c • v :=
begin 
  intros n c d,
  induction n with n hn,
  { intro v,
    cases v,
    simp, },
  { intro v,
    cases v with n head tail,
    simp,
    split,
    { linarith, },
    { exact hn tail, }, },
end

end tuple -- hide
