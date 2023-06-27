import vectors.tuple -- hide
import data.real.basic --hide
import vectors.tuple.tactics --hide
namespace tuple -- hide


/- 

# Vector world

## Level 7: `multiplicative identity` 

-/

/- Lemma

-/

lemma one_mul : ∀ {n : ℕ} (v : ℝ ^ n), (1 : ℝ) • v = v :=
begin 
  intro n,
  induction n with n hn,
  { intro v,
    cases v,
    simp, },
  { intro v,
    cases v with n head tail,
    simp,
    exact hn tail, },
end

end tuple -- hide
