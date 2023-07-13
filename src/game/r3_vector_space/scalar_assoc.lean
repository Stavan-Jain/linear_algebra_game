import game.r3_vector_space.scalar_dist_1
namespace tuple -- hide


/- 

# R³ Vector Space World 

Strategy:
The ring tactic which helps in proving various commutative rings (e.g. applying ring to  "a • b • c = a • c • b" resolves the goal by applying commutativity as needed ) may be helpful here.


## Level 6: `scalar_assoc` 

-/

/- Lemma
c • d • u = (c * d) • u
-/

lemma scalar_assoc : ∀ (c d : ℝ) (u : ℝ ^ 3), c • d • u = (c * d) • u :=
begin 
  intros c d u,
  cases_tuple u 3,
  simp,
  exact ⟨by ring, by ring, by ring⟩,
end

end tuple -- hide
