import vectors.tuple -- hide
import vectors.tuple.tactics --hide
import data.real.basic --hide
namespace tuple -- hide

/- 
# Auxiliary Theorems

## Level 1: `Vector_dist` 

-/

/- Lemma
(cx)·y=c (x·y) for all x, y ∈ ℝⁿ and c ∈ R
-/

lemma vector_dist : ∀ {n : ℕ} (c d : ℝ) (v : ℝ ^ n),  (c + d) • v = c • v + d • v :=
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
