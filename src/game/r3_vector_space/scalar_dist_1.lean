import game.r3_vector_space.vec_add_neg --hide
namespace tuple -- hide


/- 

# R³ Vector Space World 

Strategy:
"cases_tuple v 3" and "ring" may come in handy here as well. 

## Level 5: `Distributive property 1` 

-/

/- Lemma
c • u + c • v
-/

lemma scalar_dist_1 : ∀ (c : ℝ) (u v : ℝ ^ 3), c • (u + v) = c • u + c • v :=
begin 
  intros c u v,
  cases_tuple u 3,
  cases_tuple v 3,
  simp,
  exact ⟨by ring, by ring, by ring⟩,
end

end tuple -- hide
