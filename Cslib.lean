def hello := "world"


class Boolean (α : Type u) where
  xor : α → α → α 
  and : α → α → α
  or  : α → α → α
  not : α → α
  bfalse : α
  btrue : α

-- instance : Max Rat where
--   max := fun a => fun b => if a > b then a else b

-- instance : Min Rat where
--   min := fun a => fun b => if a < b then a else b

-- /-
--   Treat -1 as true and 1 as false
-- -/
-- instance : Boolean Rat where
--   xor := fun x => fun y => x * y
--   and := fun x => fun y => max x y
--   not := fun x => -1 * x
--   or := fun x => fun y => min x y
--   bfalse := 1
--   btrue := -1


-- def boolean_sum {n : Nat} {α : Type u} [Boolean α] (x : Vector α n) := 
--   (Vector.foldl (· xor ·) 0 x) 1

-- -- TODO: better definition??
-- -- def vector_innerprod {n : Nat} {α : Type u} [Boolean α] (x y : Vector α n) : α := 
-- --   Vector.map₂ (· Boolean.band ·) x y
-- --   |>.toList
-- --   |>.foldl Boolean.xor Boolean.bfalse

-- -- -- infixr:35 " ⬝ " => ∑ i in range Vector.map₂ (·*·)


-- -- def BoolFunc {n : Nat} {α : Type u } [Boolean α]  := (Vector (Boolean α)  n) → (Boolean α)

-- -- -- Wait is the below actually right?
-- -- -- TODO: cast the bellow?
-- -- -- TODO: how do we do this ± 1 thing
-- -- def χ {n : Nat} {α : Type u} (S : Vector Boolean n) := fun (x : Vector (Boolean α) n) => vector_innerprod x S
-- -- -- def χ {n : Nat} [Boolean α] (S : Vector Bool n) : BoolFunc := fun (x : ) => x ⬝ S

-- -- def function_inner_product {n : Nat} (x y : BoolFunc n) := 
-- --   1 / (Rat.pow 2 n) * (∑ i in (Finset.range (2^n)), (x i) * (y i))

-- -- def fourier_coefficient {n : Nat} (x : BoolFunc n) (S : Vector (Boolean α) n) := 
-- --   function_inner_product x (χ S)

-- -- def fourier_function {n : Nat} (f : BoolFunc n) := 
-- --   fun (S : Vector (Boolean α) n) => fourier_coefficient f S * (χ S)

-- -- theorem Plancherel_Theorem {n : Nat} (f g: BoolFunc n) : function_inner_prod f g = function_inner_prod (fourier_function f) (fourier_function g) 
-- --   := sorry

-- -- theorem Parseval_Theorem {n : Nat} (f : BoolFunc n) : function_inner_prod f f = function_inner_prod (fourier_function f) (fourier_function f) 
-- --   := sorry
  