import game.dot_prod_world.zero_dot --hide

namespace tuple -- hide

/- 
# Vector world

Strategy:
Think about how we can use zero_dot to prove dot_zero.

## Level 4: `vector dot zero is zero` 

-/

/- Lemma
x ⬝ 0 = 0 ∀x ∈ Rⁿ 
-/


lemma dot_zero: ∀ {n : ℕ} (x : ℝ ^ n), x ⬝ 0 = 0 :=
begin 
  intros, 
  rw dot_comm, 
  exact zero_dot x,  
end

end tuple -- hide