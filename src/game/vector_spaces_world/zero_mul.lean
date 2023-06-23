import vectors.tuple -- hide
import data.real.basic --hide
import vectors.tuple.tactics --hide
namespace tuple -- hide


/- 

# Vector world

## Level 8: `zero_mul` 

-/

/- Lemma

-/

lemma zero_mul : ∀ {n :ℕ } (u : tuple n), 0**u = 0 :=
begin
  intro n,
  induction n with n hn,
  {intro u, cases u,
  simp, 
  refl,},
  {intro u, cases u,
  simp,
  rw hn,}, 
end

end tuple -- hide