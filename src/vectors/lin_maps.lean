import vectors.tuple

@[simp]
def linear_transformation {n m : ℕ} (T : ℝ^ n  → ℝ ^ m ) : Prop :=
∀ (c d: ℝ) (x : ℝ ^ n) (y : ℝ ^ n ), T ((c • x) +(d• y)) = c • (T x) + d•(T y)

