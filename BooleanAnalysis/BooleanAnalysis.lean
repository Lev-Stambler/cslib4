
import Mathlib.Data.Vector
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic.Linarith
-- import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Basic
import BooleanAnalysis.BooleanVector
import LLMstep
import Mathlib.Data.Fintype.Vector
import Mathlib.Data.Setoid.Partition
-- import Mathlib.Probability.Notation

open Vector BigOperators Finset
open Classical

-- def

#check (n: Nat) → { i : Nat // i < n  }


class OfInt (α : Type u) (_ : Int) where
  /-- The `OfNat.ofNat` function is automatically inserted by the parser when
  the user writes a numeric literal like `1 : α`. Implementations of this
  typeclass can therefore customize the behavior of `n : α` based on `n` and
  `α`. -/
  ofInt : α


instance : OfNat Bool n where
  ofNat := match n with
    | 1 => true
    | _ => false

def Bool.toInt (b : Bool) : Int := if b then -1 else 1
def Bool.toRat (b : Bool) : Rat := if b then -1 else 1

#eval (0 : Bool)
#eval (1 : Bool)


-- class BooleanF (α : Type u) where
--   xor : α → α → α
--   and : α → α → α
--   or  : α → α → α
--   not : α → α
--   bfalse : α
--   btrue : α

#eval Max.max (-1) (2)


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

#check Fin.fintype 10

-- -- TODO: better definition??
-- TODO: big oplus for XOR syntax
def vector_innerprod_bool {n : Nat} (x y : BoolVec n) : Bool :=
  fold (Bool.xor : Bool → Bool → Bool) true (fun j => ((x.get j) ∧  (y.get j))) (Fin.fintype n).elems

def vector_innerprod {n : Nat} (x y : BoolVec n) : Rat :=
  ↑ (vector_innerprod_bool x y).toRat
-- def vector_innerprod {n : Nat} (x y : BoolVec n) : Rat :=
--   ∏ j : Fin n,  Bool.toRat ((x.get j) ∧  (y.get j))
  -- Vector.map₂ (and . .) x y
  -- |>.toList
  -- |>.foldl xor false

infixr:75 " ⬝ " => (vector_innerprod . .)


def BooleanFunc {n : Nat}  := (Vector Bool n) → Rat

def BooleanFinset := Finset.image Bool.toRat Finset.univ
#check BooleanFinset

-- -- -- Wait is the below actually right?
-- -- -- TODO: cast the bellow?
-- -- -- TODO: how do we do this ± 1 thing
def χ {n : Nat} (S : BoolVec n) : BooleanFunc (n := n) := fun (x : BoolVec n) =>
  x ⬝ S
-- def χ {n : Nat} [Boolean α] (S : BoolVec n) : BooleanFunc := fun (x : ) => x ⬝ S


def expecation {n : Nat} (f : BooleanFunc (n := n)) : Rat :=
  (∑ i : Vector Bool n, f i) / 2^n

notation "𝔼[" f "]" => expecation f

def function_innerprod {n : Nat} (f g : BooleanFunc (n := n)) : Rat  :=
  let inner : BooleanFunc (n := n) := fun (x : BoolVec n) => f x * g x
  𝔼[inner]

def function_innerprod_unnorm {n : Nat} (f g : BooleanFunc (n := n)) : Rat  :=
  -- let inner : BooleanFunc (n := n) := fun (x : BoolVec n) => f x * g x
  ∑ i : Vector Bool n, f i * g i

lemma function_innerprod_unnorm_eq (f g : BooleanFunc (n := n)) :
  (∑ i : Vector Bool n, f i * g i) = function_innerprod_unnorm f g := by rfl

theorem function_innerprod_unnorm_def {n : Nat} (f g : BooleanFunc (n := n)) :
  function_innerprod_unnorm f g / 2^n = function_innerprod f g := by
    simp [function_innerprod, expecation, function_innerprod_unnorm]

def Fourier_coefficient {n : Nat} (f : BooleanFunc (n := n)) (S : BoolVec n) :=
  function_innerprod f (χ S)

-- TODO: maybe we can't **really** use Rat... we have to use boolean/ true false maybe and then write this inhab for it
def Fourier_function {n : Nat} (f : BooleanFunc (n := n)) : BooleanFunc (n := n) :=
  fun (S : BoolVec n) => Fourier_coefficient f S

def symm_diff {n : Nat} (S₁ S₂ : BoolVec n) : BoolVec n:=
  ofFn (fun i => if S₁.get i = S₂.get i then false else true)
  -- Vector.map₂ (fun x => fun y => if x = y then false else true) S₁ S₂
  -- _function_sum _symm_diff ⟨2^n - 1, by sorry⟩ -- TODO: rm sorry

#check expecation
  -- (∑ x : Vector Bool n, f x) / 2^n

-- def dot_setoid {n : Nat} (a : Vector Bool (n := n)) : Setoid (Vector Bool n) := --Setoid.ker (fun x => vector_innerprod_bool x a)
--     ⟨fun x => fun y => x ⬝ a = y ⬝ a,
--       ⟨
--         by intro x; simp,
--         by intro x y; simp; intro h; rw [h],
--         by intro x y z; simp; intros h1 h2; rw [h1, h2]
--       ⟩
--     ⟩

-- #check Setoid.classes (dot_setoid (n := 10) (ofFn (fun _ => true)))

-- noncomputable instance {n : Nat} (a : Vector Bool (n := n)) : DecidableRel (dot_setoid (n := n) a).r :=
--   fun x y => by
--     simp [dot_setoid]
--     apply Classical.propDecidable

-- #check @Quotient.mk'' (Vector Bool 10) (dot_setoid default) --: Vector Bool n → Quotient (dot_setoid a)

-- TODO: idk how to do this but want proof that returned item is true at spot
-- def first_non_false (a : Vector Bool n) (h : a ≠ default) : ⟨Fin n, Vector.get a⟩ := sorry

lemma expec_prod_nonzero_of_0 {n' : Nat} (a : Vector Bool (n := Nat.succ n')) (ha_neq : a ≠ default) : 𝔼[χ a] = 0 := by
  let n := Nat.succ n'
  simp [expecation]
  let one_set := Finset.filter (fun x => (χ a) x  = 1) (Finset.univ : Finset (Vector Bool n))
  let neg_one_set := Finset.filter (fun x => (χ a) x = -1) (Finset.univ : Finset (Vector Bool n))

  have : ∑ x : Vector Bool n, (χ a) x  = ∑ x in one_set, (χ a) x + ∑ y in neg_one_set, (χ a) y := by
    have unioned : (Finset.univ : Finset (Vector Bool n)) = one_set ∪ neg_one_set := by
      ext x
      apply Iff.intro
      . intro h
        simp [one_set, neg_one_set, χ, vector_innerprod, Bool.toRat]
        cases vector_innerprod_bool x a with
        | false => simp
        | true => simp
      . simp
    have disjoint : Disjoint one_set neg_one_set := by
      have : ∀ ⦃a⦄, a ∈ one_set → a ∉ neg_one_set := by
        intro a h
        simp [one_set, χ] at h
        simp [neg_one_set, χ]
        rw [h]
        simp
      rwa [Finset.disjoint_left]
    rw [unioned]
    rw [Finset.sum_union disjoint]

  rw [this]
  have eq_1 : ∀ x ∈ one_set, (χ a) x = 1 := by
    intro x h
    simp [one_set] at h
    simp [h]
  have eq_neg_1 : ∀ x ∈ neg_one_set, (χ a) x = -1 := by
    intro x h
    simp [neg_one_set] at h
    simp [h]

  rw [Finset.sum_eq_card_nsmul eq_1, Finset.sum_eq_card_nsmul eq_neg_1]
  -- TODO: **this whole thing should actually be its own lemma**
  have : card one_set = card neg_one_set := by
    simp [one_set, neg_one_set, χ, vector_innerprod]
    let f : (a : Vector Bool n) → a ∈ one_set → (Vector Bool n) := fun a =>
      fun ha =>
        Vector.cons (Bool.not (Vector.head a)) (Vector.tail a)
    have h₁ :  ∀ a (ha : a ∈ one_set), f a ha ∈ neg_one_set := by
      intro x ha
      simp [one_set, χ, vector_innerprod, vector_innerprod_bool] at ha
      simp [neg_one_set, χ, vector_innerprod, vector_innerprod_bool]
      rw [← ha]
      sorry


    have h₂ : ∀ a b (ha : a ∈ one_set) (hb : b ∈ one_set) (h : f a ha = f b hb), a = b := sorry
    have h₃ : ∀ b ∈ neg_one_set, ∃ a, ∃ (ha : a ∈ one_set), f a ha = b := sorry

    exact Finset.card_congr f h₁ h₂ h₃

  rw [this]
  simp





-- TODO: what here
lemma expec_prod_nonzero_of_0' {n : Nat} (f : BooleanFunc (n := n)) :
  (∃ a,  a ≠ Inhabited.default ∧ ∀ x, f x = x ⬝ a) → (𝔼[f] = 0)  := by
  intro ⟨a, h1, h2⟩
  simp [expecation]; left
  have : ∀ x ∈ Finset.univ, f x = x ⬝ a := by
    intro x h
    apply h2
  rw [Finset.sum_congr rfl this]

  simp [Inhabited.default, *] at h1
  simp [vector_innerprod, Bool.toRat]

  let t₁ := fun x => (∏ x₁ : Fin n, if Vector.get x x₁ = true ∧ Vector.get a x₁ = true then (-1 : Rat) else (1 : Rat))
  let t₂ := fun x => (∏ x₁ : { i : Fin n // Vector.get a i = true },
    let ⟨x₁, _⟩ := x₁
    if Vector.get x x₁ = true then -1 else (1 : Rat))
  have : ∀ x ∈ Finset.univ, (t₁ x)
    = t₂ x := by sorry
  rw [Finset.sum_congr rfl this]
  /-
  The remainder of this proof is straightoforward.
  We must do induction. Base case n = 1, then straightforward
  IH assume before, split with n + 1, if n + 1 ∉ a, then we are done. Otherwise we
  split up the sum and show one is * -1 the other is * 1
  -/
  sorry


lemma expec_prod_zero_of_1 {n : Nat} (f : BooleanFunc (n := n)) :
  (∃ a, (∀ x, f x = x ⬝ a) ∧ a= Inhabited.default) → (𝔼[f] = 1)  := by
  intro ⟨a, h₁, h₂⟩
  simp [expecation]
  have : ∀ x ∈ Finset.univ, f x = x ⬝ a := by
    intro x h
    apply h₁
  rw [Finset.sum_congr _ this]
  simp [vector_innerprod]
  let t₁ := fun x => (∏ x₁ : Fin n, if Vector.get x x₁ = true ∧ Vector.get a x₁ = true then (-1 : Rat) else (1 : Rat))
  let t₂ := fun x => (∏ x₁ : { i : Fin n // Vector.get a i = true },
    let ⟨x₁, _⟩ := x₁
    if Vector.get x x₁ = true then -1 else (1 : Rat))
  have : ∀ x : Vector Bool n, (t₁ x)
    = t₂ x := by sorry
  -- rw [Fintype.sum_congr (t₁) (t₂) this]
  sorry





-- lemma function_sum_expectation {n : Nat} (f : BooleanFuncR (n := n)) :
--   _function_sum f ⟨2^n - 1, by sorry⟩ = 𝔼[x]   := sorry

theorem orthonormal_parity_func_ne {n : Nat} (S₁ S₂ : BoolVec n) :
    S₁ ≠ S₂ →
     function_innerprod_unnorm (χ (n := n) S₁) (χ (n := n) S₂) = 0 :=
  -- let χ₁ := χ (n := n) (α := Rat) S₁
  -- let χ₂ := χ (n := n) (α := Rat) S₂
  by
    intro h
    have prod : (x : BoolVec n) → χ S₁ (x) * χ S₂ (x) = χ (symm_diff S₁ S₂) x := sorry
    -- rw [prod]
    -- rw [χ₁, χ₂]
    have  :  function_innerprod_unnorm (χ S₁) (χ S₂) / 2^n = 0 / 2^n → function_innerprod_unnorm (χ S₁) (χ S₂) = 0 := by
      intro h1
      sorry -- TODO::::!!
      -- rw [Nat.zero_div]
    apply this
    rw [zero_div]
    apply expec_prod_nonzero_of_0
    use symm_diff S₁ S₂
    have : symm_diff S₁ S₂ ≠ default := by
      intro h1
      simp [symm_diff] at h1
      simp [h1] at h
      apply h
      -- have : default = ofFn (fun x => false) := by
      --   simp [default]
      simp [default] at h1
      have : ofFn (fun x => S₁.get x) = ofFn (fun x => S₂.get x) → S₁ = S₂ := by
        intro h2
        sorry
      apply this
      sorry -- AHAHHHH
    apply And.intro
    . apply this
    . intro x
      simp [χ, symm_diff]
      sorry --- AHAHA TODO:

theorem fourier_equivalence {n : Nat} (f : BooleanFunc (n := n))  :
  f = fun x => ∑ S : (Vector Bool n), ((Fourier_function f) S) * (χ S x) := by
    sorry

lemma switch_coe {n : Nat} (f g : BooleanFunc (n := n)) (S₁ S₂ : Vector Bool n): ∑ x : Vector Bool n,
            Fourier_function f S₁ * Fourier_function g S₂ * χ S₁ x * χ S₂ x = Fourier_coefficient f S₁ * Fourier_coefficient g S₂ * (
              (∑ x : Vector Bool n, χ S₁ x * χ S₂ x))
            := by sorry

theorem Plancherel_Theorem {n : Nat} (f g: BooleanFunc (n := n)) : function_innerprod f g = function_innerprod (Fourier_function f) (Fourier_function g)
  := by
    simp [function_innerprod, expecation]
    simp [Fourier_function]
    -- rw (fourier_equivalence f)
    -- rw [fourier_equivalence f, fourier_equivalence g]
    conv =>
      lhs
      rw [fourier_equivalence f, fourier_equivalence g]
      simp


    let t₁ := fun x => (∑ S : Vector Bool n, Fourier_function f S * χ S x) * (∑ S : Vector Bool n, Fourier_function g S * χ S x)
    let t₂ := fun x => ∑ S₁ : Vector Bool n, (∑ S₂ : Vector Bool n, Fourier_function f S₁ * Fourier_function g S₂ * χ S₁ x * χ S₂ x)
    have : ∀ x ∈ Finset.univ, t₁ x =
        t₂ x := by
          sorry
    rw [Finset.sum_congr rfl this]
    -- simp [t₂ x]
    have : (∑ a : Vector Bool n, t₂ a) = ∑ x : Vector Bool n, ((∑ S : Vector Bool n, Fourier_function f S * Fourier_function g S * χ S x * χ S x) +
      (∑ S₁ : Vector Bool n, ∑ S₂ : {S₂ : Vector Bool n // S₁ ≠ S₂},
        let ⟨S₂, hS₂⟩ := S₂
        Fourier_function f S₁ * Fourier_function g S₂ * χ S₁ x * χ S₂ x)) := by
      sorry
    rw [this]
    conv =>
      lhs; lhs;
      rw [Finset.sum_add_distrib]
      rhs;
      rw [Finset.sum_comm]
      rhs;
      intro S₁;
      rw [Finset.sum_comm];
      rhs; intro S₂;
      rw [switch_coe f g S₁ S₂]



      -- rhs;
    -- rw [function_innerprod_unnorm_def (χ S₁) (χ (↑S₂))]

    rw [orthonormal_parity_func_ne _ _ S₂.property]

      -- We want to move the coefficients to the front
      -- Fourier_function g S₂
    -- have :



      -- rw [orthonormal_parity_func_ne hS₂]

    -- conv =>
    --   lhs


      -- rw [t₂ ]




      -- rw [← Fintype.prod_sum ]

#check Fintype.prod_bijective



    -- show _ = (∑ x : Vector Bool n,
    --   (∑ x_1 : Vector Bool n, f x_1 * χ x x_1) / 2 ^ n * ((∑ x_1 : Vector Bool n, g x_1 * χ x x_1) / 2 ^ n)) / 2 ^ n

    sorry
-- TODO: actually do?

-- -- theorem Parseval_Theorem {n : Nat} (f : BooleanFunc n) : function_inner_prod f f = function_inner_prod (fourier_function f) (fourier_function f)
-- --   := sorry
