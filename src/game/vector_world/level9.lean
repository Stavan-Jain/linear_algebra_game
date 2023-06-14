import vectors.tuple -- hide
import data.real.basic
namespace tuple -- hide

/- 
# Vector world

## Level 9: `Cauchy-Schwarz Inequality` 

-/

/- Lemma
|x · y| ≤ ||x|| * ||y||.-/

lemma cauchy_schwarz: ∀ {n : ℕ} (x: tuple n) (y : tuple n) 
, | x ⬝ y| ≤ norm_sq x * norm_sq y :=
begin 
  sorry, 
end

end tuple -- hide