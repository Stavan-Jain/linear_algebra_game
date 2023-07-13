import game.linear_map_world.zero_transformation
namespace vector_spaces
open tuple -- hide

/- 

Now we’re getting into the interesting part of linear algebra – linear maps.
You could also call them linear transformations. 
As one of the key definitions in linear algebra, a linear map from V to W is 
a function T: V → W with the following two properties:

Additivity: T (u + v) = T u + T v for all {u v : V}
Homogeneity: T (λ v) = λ (T v) for all {λ : F} and all {v : V}

The set of all linear maps from V to W is sometimes denoted L(V, W) in math textbooks.

# Linear Transformation world

Background: In this Lean game, we define a linear transformation as a map T that satisfies
T(cx + dy) = cT(x) + dT(y).

In this level, you're given an example of a linear transformation T, and 
you are to prove that this is truely a linear transformation according to the definition of 
linear transformation given above.

Hint: Tactic "simp" is very helpful when you need to get the definition of something, 
and you can use cases_tuple to deal with a two (or more) tuple.

## Level 5: `Random linear transformation` 

-/

/- Lemma
T: R² → R² defined by T((x, y)) = (x+y, y), x, y ∈ R² is a linear transformation
-/
lemma example_1 : ∀ (T : ℝ ^ 2  → ℝ ^ 2), 
(∀ (x y : ℝ), (T [[x, y]]) = [[(x + y), y]]) → linear_transformation T ℝ :=
begin 
  intros T h,
  simp, 
  intros c d u v,
  cases_tuple u 2,
  cases_tuple v 2,
  simp,
  repeat {rw h},
  simp,
  ring, 
end

end vector_spaces -- hide