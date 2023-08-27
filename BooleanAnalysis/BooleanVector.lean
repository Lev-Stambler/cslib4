-- import Mathlib.Data.Vector
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.BigOperators.Basic
-- import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Vector
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Finset.Fin

open Vector BigOperators Fintype Classical Finset 

#check Fintype
def BoolVec (n : Nat) := Vector Bool n

instance (n : Nat) : Inhabited (BoolVec n) where
  default := Vector.ofFn (fun _ => false)