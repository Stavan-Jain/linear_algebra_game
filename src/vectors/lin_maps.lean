import vectors.vector_spaces
import vectors.tuple


/-
@[simp]
def linear_transformation {n m : ℕ} (T : ℝ^ n  → ℝ ^ m ) : Prop :=
∀ (c d: ℝ) (x : ℝ ^ n) (y : ℝ ^ n ), T ((c • x) +(d• y)) = c • (T x) + d•(T y)
-/
namespace vector_spaces

@[simp]
def linear_transformation {𝕍₁ : Type*} {𝕍₂ : Type*} (T : 𝕍₁ → 𝕍₂) (𝔽 : Type*) 
[field 𝔽] [vector_space 𝕍₁ 𝔽] [vector_space 𝕍₂ 𝔽]  
:Prop := ∀ (c d: 𝔽) (x : 𝕍₁) (y : 𝕍₁ ), T ((c • x) +(d• y)) = c • (T x) + d•(T y)


@[simp]
def kernel {n m : ℕ} (T : ℝ^ n  → ℝ ^ m ) : set (ℝ ^ n) := 
{x : ℝ ^ n | T x = 0}

@[simp]
def image {n m :ℕ} (T : ℝ ^ n  → ℝ ^ m ) : set (ℝ ^ m) :=
{b : ℝ ^ m | ∃ (x : ℝ ^ n), T x = b}

end vector_spaces