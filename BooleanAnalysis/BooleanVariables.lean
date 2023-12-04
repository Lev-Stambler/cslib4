-- import Mathlib.Data.Vector
import Mathlib.Data.Finset.Basic
import LLMstep
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Data.Fintype.Vector
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Finset.Fin
import Mathlib.Algebra.Ring.BooleanRing
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Multilinear.Basic

set_option quotPrecheck false

open Vector BigOperators Fintype Classical Finset BooleanRing Ring Real

namespace Bool
  def toReal (b : Bool) : Real := if b then -1 else 1
end Bool

namespace BoolVector

-- variable {α β : Type*} [BooleanRing α]
variable {N : Nat}

def BoolVec := Vector Bool N
#check BoolVec

def BooleanFunc  := (Vector Bool N) → Real


variable (f g : BooleanFunc (N := N))
variable (x y : BoolVec (N := N))
variable (S : BoolVec (N := N))

#check Finset.sum

noncomputable def expectionVecBool : Real :=
  (∑ i : Vector Bool N, f i) / 2^N

noncomputable def expecationBool (f : Bool → Real) : Real :=
  (∑ i : Bool, f i) / 2

notation "𝔼[" f' "]" => expectionVecBool (N := N) f'
notation "𝔼'[" f' "]" => expecationBool f'

#check 𝔼[f]

lemma expecation_eq : 𝔼[f] = (∑ i : Vector Bool N, f i) / 2^N := rfl

-- TODO: hmmmm... may need to do the Boolean first version... but then we do not get niceness of multiplication
-- Maybe lemma that ⬝ always returns 1 or -1
noncomputable def vector_innerprod : Real :=
  ∏ i : Fin N, (if x.get i then y.get i else ¬ y.get i).toReal
  -- fold (. * .) 1 (fun j => (max (x.get j).toReal (y.get j).toReal)) (Fin.fintype N).elems
  -- fold (Bool.xor : Bool → Bool → Bool) true (fun j => ((x.get j) ∧  (y.get j))) (Fin.fintype n).elems
  -- ↑ (vector_innerprod_bool x y).toReal

infixr:75 " ⬝ " => (vector_innerprod (N := N) . .)

#check ∏ i : Fin 10, if i == 0 then 1 else 2

-- TODO: how does this work???
lemma vector_space_size : (n : Nat) → Finset.card (Finset.univ : Finset (Vector Bool n)) = 2^n := by
  simp [Finset.card_univ, Finset.card_range]

theorem mult_linearity_of_expectation : (n : Nat) → (fs : Vector (Bool → Real) n) →
  expectionVecBool (N := n) (fun (v: Vector Bool n) =>  ∏ i : Fin n, (Vector.get fs i) (Vector.get v i)) = ∏ i : Fin n, 𝔼'[Vector.get fs i]
  | Nat.zero, fs => by
    simp [expectionVecBool, expecationBool]
  | Nat.succ n, fs => by
    simp [expectionVecBool, expecationBool]
    have : (∏ x : Fin (Nat.succ n), (Vector.get fs x true + Vector.get fs x false)) / 2 ^ Nat.succ n
      = ((∏ x : Fin n, (Vector.get fs.tail x true + Vector.get fs.tail x false)) / 2 ^ n) * (fs.head true + fs.head false) / 2 := by
      sorry
    rw [this]
    have : (∏ x : Fin n, (Vector.get fs.tail x true + Vector.get fs.tail x false)) / 2 ^ n = ∏ x : Fin n, 𝔼'[Vector.get fs.tail x] := by
      simp
    rw [this]
    rw [←mult_linearity_of_expectation n (fs.tail), expectionVecBool]
    sorry


  --  := by
  --   -- TODO: fix up expec..
  --   simp [expectionVecBool, expecationBool]
  --   exact Nat.recOn N
  --     (by
  --       simp
  --     )
  --     (fun n ih => by
  --       -- have incI : Fin.ofNat (Nat.succ n) ∈ (Finset (Fin (Nat.succ n))) := by
  --       --   simp
  --       have : (∏ x : Fin (Nat.succ n), (Vector.get fs x true + Vector.get fs x false)) / 2 ^ Nat.succ n

  --       rw [prod_eq_mul_prod_diff_singleton _]
  --       sorry
  --     )


noncomputable def χ (S : BoolVec (N := N)) : BooleanFunc (N := N) :=
  (fun (v : BoolVec (N := N)) => (v ⬝ S))

def innerprod_decomposed : Vector (Bool → Real) N := Vector.ofFn
  (fun i => (fun (b : Bool) => (if S.get i then b else ¬b).toReal))

lemma χ_eq_prod_of_fns (S : BoolVec (N := N)) :
  χ S = fun v => ∏ i : Fin N, ((innerprod_decomposed S).get i) (v.get i) := by
  sorry


def nonzero (a : Vector Bool N) : Prop := ∃ i : Fin N, a.get i = true

lemma expec_prod_nonzero_of_0 (a : Vector Bool N) (ha_neq : nonzero (N := N) a) : 𝔼[χ a] = 0 := Exists.elim ha_neq
  (fun i => by
    intro hi
    rw [χ_eq_prod_of_fns, mult_linearity_of_expectation]
    have :  𝔼'[Vector.get (innerprod_decomposed a) i] = 0 := by
      rw [expecationBool]
      simp; simp [innerprod_decomposed]; rw [hi]
      simp; simp [Bool.toReal]


    rw [Finset.prod_eq_zero_iff]
    use i
    have huniv : i ∈ univ := by simp
    exact ⟨huniv, this⟩

    -- rw [mult_linearity_of_expectation]
  )




-- lemma BoolVec.add_comm (x y : BoolVec (α := α) N) : x + y = y + x := by
--   apply Vector.ext
--   intro i
--   simp [Vector.get]
--   cases x
--   cases y

--   rw [AddCommMonoid.add_comm]
--   -- rw [add_comm]


#check BooleanRing
-- instance Module
-- class BooleanRing (α) extends Ring α where
-- class BooleanRing (α : Type*) where
--   xor : α → α → α
--   xor_comm : ∀ a b : α, xor a b = xor b a
--   xor_assoc : ∀ a b c : α, xor (xor a b) c = xor a (xor b c)
--   xor_self : ∀ a : α, xor a a = 0
--   xor_zero : ∀ a : α, xor a 0 = a
--   xor_one : ∀ a : α, xor a 1 = a
--   xor_inv : ∀ a : α, xor a a = 0
--   xor_iden : ∀ a : α, xor a 0 = a
--   xor_iden : ∀ a : α, xor a 1 = a

-- structure BoolVec where
--   get : Fin N → Bool

#check Fintype
-- def BoolVec [α : BooleanRing] := Vector α N

def BoolFunc (n : Nat) := BoolVec n → ℝ

instance : IsCommutative Bool Bool.xor := ⟨
  by
    intro a b
    cases a <;> cases b <;> (simp [Bool.xor];)
⟩

instance : IsAssociative Bool Bool.xor := ⟨
  by
    intro a b c
    cases a <;> cases b <;> cases c <;> (simp [Bool.xor];)
  ⟩

def Bool.toInt (b : Bool) : Int := if b then -1 else 1
def Bool.toRat (b : Bool) : Rat := if b then -1 else 1

def vector_innerprod_bool {n : Nat} (x y : BoolVec n) : Bool :=
  fold (Bool.xor : Bool → Bool → Bool) true (fun j => ((x.get j) ∧  (y.get j))) (Fin.fintype n).elems
  -- TODO: maybe we need to define inner prod in terms of a multiplication

def vector_innerprod {n : Nat} (x y : BoolVec n) : Rat :=
  ↑ (vector_innerprod_bool x y).toRat

infixr:75 " ⬝ " => (vector_innerprod . .)



-- instance (n : Nat) : MeasurableSpace (BoolVec n) where
--   MeasurableSet' := fun _ => true
--   measurableSet_empty := rfl
--   measurableSet_compl := by
--     intro _
--     simp
--   measurableSet_iUnion := by
--     intro _ _
--     rfl

-- def discrete_meas (n : Nat) : (∀ s : Set (BoolVec n), MeasurableSet s → ℝ≥0∞) := by
--   intro s
--   sorry

-- lemma zero_empty_set (n : Nat) : (discrete_meas n) ∅ MeasurableSet.empty = 0 := sorry

-- lemma disjoint_sum_meas (n : Nat) :
--       ∀ ⦃f : ℕ → Set (BoolVec n)⦄ (h : ∀ i, MeasurableSet (f i)),
--         Pairwise (Disjoint on f) → (discrete_meas n) (⋃ i, f i) (MeasurableSet.iUnion h) = ∑' i, (discrete_meas n) (f i) (h i) := sorry

-- noncomputable def MeasureBoolVec (n : Nat) : Measure (BoolVec n) := Measure.ofMeasurable
--   (
--     discrete_meas n
--   )
--   (
--     zero_empty_set n
--   )
--   (
--     disjoint_sum_meas n
--   )


-- noncomputable instance (n : Nat) : MeasureSpace (BoolVec n) where
--   volume := MeasureBoolVec n

-- #check fun (X : BoolFunc 10) => ∫ a, X a

instance (n : Nat) : Inhabited (BoolVec n) where
  default := Vector.ofFn (fun _ => false)

end BoolVector
