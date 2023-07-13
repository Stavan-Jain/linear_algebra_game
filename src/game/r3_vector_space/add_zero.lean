import game.r3_vector_space.vec_comm--hide
namespace tuple -- hide


/- 

# Vector world

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
