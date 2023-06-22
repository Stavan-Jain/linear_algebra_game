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

lemma vec_assoc : ∀ {n :ℕ } (u v w : tuple n), u + (v + w) = u + v + w :=
begin 
  intro n, 
  induction n with n hn,
  {intros u v w,
  casesm* (tuple 0),
  simp,},
  {intros u v w,
  casesm* (tuple n.succ),
  simp,
  split,
  {linarith,},
  {rw hn,},},
end

end tuple -- hide