import vectors.tuple -- hide
import data.real.basic --hide
import vectors.tuple.tactics --hide
namespace tuple -- hide


/- 

# Vector world

## Level 1: `vector_assoc` 

-/

/- Lemma

-/

lemma vec_assoc : ∀ {n : ℕ} (u v w : ℝ ^ n), u + (v + w) = u + v + w :=
begin
  intro n,
  induction n with n hn,
  { intros u v w,
    casesm* (ℝ ^ 0),
    simp, },
  { intros u v w,
    cases u with n u₁ uₙ,
    cases v with n v₁ vₙ,
    cases w with n w₁ wₙ,
    simp,
    split,
    { linarith, },
    { exact hn uₙ vₙ wₙ, }, },
end

end tuple -- hide
