import vectors.tuple

@[simp]
def linear_transformation {n m : ℕ} (T : ℝ^ n  → ℝ ^ m ) : Prop :=
∀ (c d: ℝ) (x : ℝ ^ n) (y : ℝ ^ n ), T ((c • x) +(d• y)) = c • (T x) + d•(T y)

@[simp]
def kernel {n m : ℕ} (T : ℝ^ n  → ℝ ^ m ) : set (ℝ ^ n) := 
{x : ℝ ^ n | T x = 0}

@[simp]
def image {n m :ℕ} (T : ℝ ^ n  → ℝ ^ m ) : set (ℝ ^ m) :=
{b : ℝ ^ m | ∃ (x : ℝ ^ n), T x = b}