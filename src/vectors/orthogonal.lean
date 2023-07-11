import vectors.tuple

namespace tuple


universe u
variables {α : Type u} [has_add α] [has_mul α] [has_zero α]


@[simp]
def orthogonal {n : ℕ} (x y : α ^ n) : Prop := x ⬝ y = 0


infix ` ⟂ `:63 := orthogonal
infix ` ⊥ `:63 := orthogonal


end tuple
