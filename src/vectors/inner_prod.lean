import vectors.tuple

@[simp]
def orthogonal {n : ℕ} (x y : ℝ ^ n) : Prop := x ⬝ y = 0

infix ` ⟂ `:63 := orthogonal
infix ` ⊥ `:63 := orthogonal
