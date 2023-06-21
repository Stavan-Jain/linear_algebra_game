import vectors.tuple

@[simp]
def orthogonal {n : ℕ} (x : tuple n) (y:tuple n) : Prop :=
x ⬝ y = 0 

infix ` ⟂ `:63 := orthogonal
infix ` ⊥ `:63 := orthogonal
