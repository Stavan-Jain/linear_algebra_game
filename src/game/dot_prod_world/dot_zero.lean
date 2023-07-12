import game.dot_prod_world.zero_dot --hide

namespace tuple -- hide

/- 
# Vector world

## Level 6: `vector dot zero is zero` 

-/

/- Lemma

-/


lemma dot_zero: ∀ {n : ℕ} (x : ℝ ^ n), x ⬝ 0 = 0 :=
begin 
  intros, 
  rw dot_comm, 
  exact zero_dot x,  
end

end tuple -- hide