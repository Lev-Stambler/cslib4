-- -- import Mathlib.Data.List.Count
-- -- open List Countp
-- import Mathlib.Data.Fintype.Vector
-- import Mathlib.Probability.Notation
-- import Mathlib.Probability.Independence.Basic
-- import Mathlib.MeasureTheory.Measure.VectorMeasure
-- import Mathlib.MeasureTheory.Measure.MeasureSpace

-- open Vector ProbabilityTheory MeasureTheory
-- -- import Mathlib.
-- -- import Mathlib.Probability.Independence.Kernel
-- -- open Basic

-- def MeasureSpaceVec (n : Nat) := MeasureSpace (Vector Bool n)
-- def BooleanFunc (n : Nat)  := (Vector Bool n) → ℝ

-- -- def expecation {n : Nat} (f : BooleanFunc n) : Rat := 𝔼[f] 


-- #print MeasureSpaceVec

-- def f : BooleanFunc 1 := fun v => if v.get 0 = v.get 1 then 1 else 0

-- instance : Finset (Vector Bool 1) := sorry

-- #check 𝔼[f]

-- noncomputable def exp := 𝔼[f]
 
-- --  ./lake-packages/mathlib/././Mathlib/Lean/Meta.lean:140:9: error: invalid field 'countp', the environment does not contain 'List.countp'
