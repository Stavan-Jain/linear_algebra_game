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

lemma one_mul : ∀ {n :ℕ } (u: tuple n), 1**u = u :=
begin 
  intro n,
  induction n with n hn,
  {intro u, cases u,
  simp,},
  {intro u, cases u,
  simp,
  rw hn,},
end

end tuple -- hide