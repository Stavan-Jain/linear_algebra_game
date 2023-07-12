import game.r3_vector_space.add_zero --hide

namespace tuple -- hide


/- 

# Vector world

## Level 4: `additive inverse` 

-/

/- Lemma

-/

lemma vec_add_neg : ∀ (v : ℝ ^ 3), v + -v = 0 :=
begin
  intros v,
  cases_tuple v 3,
  simpa,
end

end tuple -- hide
