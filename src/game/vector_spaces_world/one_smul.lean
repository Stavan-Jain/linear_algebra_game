import vectors.tuple -- hide
import data.real.basic --hide
import vectors.tuple.tactics --hide
import game.vector_spaces_world.scalar_assoc --hide
namespace tuple -- hide


/- 

# Vector Spaces World

Strategy:
This will give you more practice with induction!

## Level 7: `one_smul` 

-/

/- Lemma

-/

lemma one_smul {n : ℕ} : ∀ (v : ℝ ^ n ), (1 : ℝ) • v = v :=
begin 
  intros,  
  induction n with d hd,
  { cases v with n vn, 
   simp, }, 
  { cases v, 
    simp, 
    rw hd, },
end

end tuple -- hide