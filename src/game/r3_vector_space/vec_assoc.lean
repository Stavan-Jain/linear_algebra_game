import vectors.tuple -- hide
import data.real.basic --hide
import vectors.tuple.tactics --hide
namespace tuple -- hide


/- 

# ℝ^3 subspace world

## Level 1: `vector_assoc` 

-/

/- Lemma
u + (v + w) = u + v + w  ∀u,v,w ∈ R³
-/

lemma vec_assoc : ∀ (u v w : ℝ ^ 3), u + (v + w) = u + v + w :=
begin
  intros u v w,
  cases_tuple u 3,
  cases_tuple v 3,
  cases_tuple w 3,
  simp,
  exact ⟨by ring, by ring, by ring⟩,
end

end tuple -- hide
