import mynat.definition -- hide
import mynat.add -- hide
import game.world2.level5 -- hide
import tactic.ring -- hide
namespace mynat -- hide



/-

# Tutorial World

## Level 8: The simp tactic

`Simp` tactic is a tactic which tries
to prove equalities using facts in its database.


## Details

The `simp` tactic does basic automation. By level 6 of
Addition World you
have proved enough about addition for `simp` to be able
to solve all equalities whose proofs involve a tedious number
of rewrites of `add_assoc` and `add_comm`, and by
level 9 of Multiplication World the same is true of `mul_assoc` and `mul_comm`.

### Example:
If our goal is this:
```
⊢ a + b + c + d + e = c + (b + e + a) + d
```

and you have completed addition world, then you've proved
enough about addition to solve this level with `simp`. 
Note however that you can't prove `add_assoc` with `simp`,
because `add_assoc` is an ingredient to get `simp` working.

### Example:
If our goal is this:
```
⊢ a * b * c = c * b * a
```
then as long as you've completed Multiplication World, `simp` will close this
goal.
-/