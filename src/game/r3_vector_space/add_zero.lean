import game.r3_vector_space.vec_comm--hide
namespace tuple -- hide


/- 

# R³ Vector Space World 

Strategy:
Here we will have to prove that the two sides of the equation are equal.
"cases_tuple v 3" allows you to express a vector v as a tuple with 3 elements : [[v1, v2, v3]].

## Level 3: `add_zero` 

-/

/- Lemma
u + 0 = u ∀u ∈ R³   
-/

lemma add_zero : ∀ (u : ℝ ^ 3), u + 0 = u :=
begin
  intro u,
  cases_tuple u 3,
  simp,
end

end tuple -- hide
