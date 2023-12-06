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

def BoolVec.add (x y : BoolVec (N := N)) : BoolVec (N := N) := Vector.ofFn
  (fun i => (if x.get i = true then ¬ y.get i else y.get i))

variable (f g : BooleanFunc (N := N))
variable (x y : BoolVec (N := N))
variable (S T : BoolVec (N := N))

#check Finset.sum

noncomputable def expectionVecBool : Real :=
  (∑ i : Vector Bool N, f i) / 2^N

noncomputable def expecationBool (f : Bool → Real) : Real :=
  (∑ i : Bool, f i) / 2

noncomputable def func_innerpord (f g : BooleanFunc (N := N)) : Real :=
  (∑ i : Vector Bool N, f i * g i) / 2^N

notation "𝔼[" f' "]" => expectionVecBool (N := N) f'
notation "𝔼'[" f' "]" => expecationBool f'
notation:max "⟪" f "," g "⟫" => func_innerpord (N := N) f g


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
    calc
      -- TODO: head and tails not right!!
      (∑ x : Vector Bool (Nat.succ n), ∏ i : Fin (Nat.succ n), Vector.get fs i (Vector.get x i)) / 2 ^ Nat.succ n =
        (∑ x : Vector Bool (Nat.succ n), ((∏ i : Fin n, Vector.get fs i (Vector.get x i)) * Vector.get fs n.succ (Vector.get x n.succ))) / 2 ^ Nat.succ n := by sorry
      _ = (∑ x : Vector Bool n, ∏ i : Fin n, Vector.get fs i (Vector.get x i)) * (Vector.get fs n.succ true + Vector.get fs n.succ false) / 2 ^ Nat.succ n := by sorry
      _ = (∑ x : Vector Bool n, ∏ i : Fin n, Vector.get (fs.drop 1) i (Vector.get x i)) * ((Vector.get fs n + 2) true + (Vector.get fs n + 1) false) / 2 ^ Nat.succ n := by sorry
      _ = (∑ x : Vector Bool n, ∏ i : Fin n, Vector.get (fs.drop 1) i (Vector.get x i)) / 2 ^ n * ((Vector.get fs n + 1) true + (Vector.get fs n + 1) false) / 2 := by sorry
      _ = (expectionVecBool (N := n) (fun (v: Vector Bool n) =>  ∏ i : Fin n, (Vector.get (fs.drop 1) i) (Vector.get v i))) * ((Vector.get fs n + 1) true + (Vector.get fs n + 1) false) / 2 := by sorry

    rw [mult_linearity_of_expectation n (fs.drop 1)]
    simp [expecationBool]
    -- TODO: this
    sorry

noncomputable def χ (S : BoolVec (N := N)) : BooleanFunc (N := N) :=
  (fun (v : BoolVec (N := N)) => (v ⬝ S))

def innerprod_decomposed : Vector (Bool → Real) N := Vector.ofFn
  (fun i => (fun (b : Bool) => (if S.get i then b else ¬b).toReal))

lemma χ_eq_prod_of_fns (S : BoolVec (N := N)) : χ S = fun v => ∏ i : Fin N, ((innerprod_decomposed S).get i) (v.get i) := by
  apply funext
  intro v
  simp [χ, vector_innerprod, innerprod_decomposed]
  have : ∀ x : Fin N, (if Vector.get v x = true then S.get x else decide (S.get x = false)) =
    (if Vector.get S x = true then Vector.get v x else decide (Vector.get v x = false)) := by
      intro x
      cases (Vector.get v x) <;> (simp; cases (Vector.get S x) <;> simp)
  simp [this]

def nonzero (a : Vector Bool N) : Prop := ∃ i : Fin N, a.get i = true

lemma expec_prod_nonzero_eq_0 (a : Vector Bool N) (ha_neq : nonzero (N := N) a) : 𝔼[χ a] = 0 := Exists.elim ha_neq
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
  )

/--
  We can note that symmetric difference is the same as addition in the Boolean ring
-/
lemma chi_mul_chi_eq_symm_diff (S T : BoolVec (N := N)) : (fun v => (χ S v * χ T v)) = fun v => χ (BoolVec.add S T) v := by
  apply funext
  sorry


lemma expec_chis_eq_0 (hNeq : S ≠ T) : ⟪χ S, χ T⟫  = 0 := by
  rw [func_innerpord]
  conv =>
    lhs; lhs; rhs;
  rw [chi_mul_chi_eq_symm_diff]
  have : nonzero (BoolVec.add S T) := by
    sorry
  have expDefn : (∑ v : Vector Bool N, χ (BoolVec.add S T) v) / 2 ^ N = 𝔼[χ (BoolVec.add S T)] := by
    rfl

  rw [expDefn, expec_prod_nonzero_eq_0 (BoolVec.add S T) this]


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
