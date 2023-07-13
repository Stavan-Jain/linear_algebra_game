import vectors.tuple -- hide
import data.real.basic --hide
import vectors.tuple.tactics --hide
import game.vector_spaces_world.vec_assoc --hide
namespace tuple -- hide


/- 

# Vector Spaces World

Strategy:
"casesm" (short for cases_matching) allows you to apply cases in a spcific manner. 
(Remmeber, cases can be used to decompose any element of an inductively defined type. It breaks a vector of length n
into a two tuple, with first element ∈ R and second element being of length n-1.)

## Level 2: `vector_comm` 
-/

/- Lemma
u + v = v + u
-/

lemma vec_comm : ∀ {n : ℕ} (u v : ℝ ^ n), u + v = v + u :=
begin
  intro n,
  induction n with n hn,
  { intros u v,
    casesm* (ℝ ^ 0),
    refl, },
  { intros u v,
    cases u with n u₁ uₙ,
    cases v with n v₁ vₙ,
    simp,
    split,
    { linarith, },
    { exact hn uₙ vₙ, }, },
end

end tuple -- hide
