import vectors.tuple

def orthogonal {n : ℕ} (x : tuple n) (y:tuple n) : Prop :=
x ⬝ y = 0 