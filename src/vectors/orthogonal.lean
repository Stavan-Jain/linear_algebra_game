import vectors.tuple

@[simp]
def orthogonal {n : ℕ} (x : tuple n) (y:tuple n) : Prop :=
x ⬝ y = 0 

infix ` ⟂ `:45 := orthogonal
infix ` ⊥ `:45 := orthogonal

#check orthogonal [[0, 0 , 0]] [[2, 3, 4]]
#check [[0, 0 , 0]] ⊥ [[2, 3, 4]]