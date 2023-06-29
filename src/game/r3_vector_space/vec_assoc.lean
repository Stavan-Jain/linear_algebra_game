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

lemma vec_assoc : ∀ (u v w : ℝ ^ 3), u + (v + w) = u + v + w :=
begin
  intros u v w,

  cases u with _ u₁ tail,
  cases tail with _ u₂ tail,
  cases tail with _ u₃ tail,
  cases tail,

  cases v with _ v₁ tail,
  cases tail with _ v₂ tail,
  cases tail with _ v₃ tail,
  cases tail,

  cases w with _ w₁ tail,
  cases tail with _ w₂ tail,
  cases tail with _ w₃ tail,
  cases tail,

  simp,
  split, ring_nf,
  split; ring_nf,
end

end tuple -- hide
