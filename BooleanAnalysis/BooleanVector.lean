-- import Mathlib.Data.Vector
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.BigOperators.Basic
-- import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Vector
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Finset.Fin
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Decomposition.Lebesgue


open Vector BigOperators Fintype Classical Finset MeasureTheory ENNReal NNReal
open MeasurableSpace


#check Fintype
def BoolVec (n : Nat) := Vector Bool n
def BoolFunc (n : Nat) := BoolVec n → ℝ

instance (n : Nat) : MeasurableSpace (BoolVec n) where
  MeasurableSet' := fun _ => true
  measurableSet_empty := rfl
  measurableSet_compl := by
    intro _
    simp
  measurableSet_iUnion := by
    intro _ _
    rfl

def discrete_meas (n : Nat) : (∀ s : Set (BoolVec n), MeasurableSet s → ℝ≥0∞) := by
  intro s
  sorry

lemma zero_empty_set (n : Nat) : (discrete_meas n) ∅ MeasurableSet.empty = 0 := sorry

lemma disjoint_sum_meas (n : Nat) :
      ∀ ⦃f : ℕ → Set (BoolVec n)⦄ (h : ∀ i, MeasurableSet (f i)),
        Pairwise (Disjoint on f) → (discrete_meas n) (⋃ i, f i) (MeasurableSet.iUnion h) = ∑' i, (discrete_meas n) (f i) (h i) := sorry

noncomputable def MeasureBoolVec (n : Nat) : Measure (BoolVec n) := Measure.ofMeasurable
  (
    discrete_meas n
  )
  (
    zero_empty_set n
  )
  (
    disjoint_sum_meas n
  )


noncomputable instance (n : Nat) : MeasureSpace (BoolVec n) where
  volume := MeasureBoolVec n

#check fun (X : BoolFunc 10) => ∫ a, X a

instance (n : Nat) : Inhabited (BoolVec n) where
  default := Vector.ofFn (fun _ => false)
