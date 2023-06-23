import vectors.tuple -- hide
import data.real.basic --hide
import vectors.tuple.tactics --hide
namespace tuple -- hide


/- 

# Vector world

## Level 3: `add_zero` 

-/

/- Lemma

-/

lemma add_zero : ∀ {n :ℕ } (u : tuple n), u + 0 = u :=
begin 
  intro n,
  induction n with n hn,
  {intro v, cases v,
  refl,},
  {intro v,
  cases v with n head tail,
  simp,
  exact hn tail,},
end

end tuple -- hide