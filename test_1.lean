--import Mathlib
import Mathlib.Algebra.Group.Basic

-- 导入群论基础
import Mathlib.Algebra.Group.Defs

import Mathlib.Data.Nat.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Tactic.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

open Real


#check Nat.mul_succ      -- ℕ → ℕ → ℕ
#check Nat.add_one       -- ℕ → ℕ
#check Nat.one_mul       -- ∀ a : ℕ, 1 * a = a

--Addition
theorem Nat.add_comm_1 : ∀ a b : ℕ, a + b = b + a :=
by
  intros a b
  exact Nat.add_comm a b

theorem Nat.add_comm_2 (a b : ℕ) : a + b = b + a :=
Nat.add_comm a b

--Multiplying by Zero on the Left
theorem zero_mul_nat (a : ℕ) : 0 * a = 0 :=
  Nat.zero_mul a

--Multiplying by one on the Left
theorem muli_one (a : ℕ) : a * 1 = a :=
Nat.mul_one a

theorem leftIdentity (a : ℕ) : 1 * a = a :=
  Nat.one_mul a

--Multiplying by one on the right
theorem one_muli (a : ℕ) : 1 * a = a :=
Nat.one_mul a

--Associativity of Addition
theorem add_assoc_nat (a b c : ℕ) : (a + b) + c = a + (b + c) :=
Nat.add_assoc a b c

--Associativity of Multiplication
theorem mul_assoc_nat (a b c : ℕ) : (a * b) * c = a * (b * c) :=
Nat.mul_assoc a b c

--Distributivity of Multiplication over Addition
theorem mul_add_nat (a b c : ℕ) : a * (b + c) = a * b + a * c :=
Nat.mul_add a b c

theorem square_expansion (a b : ℕ) : a * a + 2 * a * b + b * b = (a + b) * (a + b) := by
  ring

theorem add_le_add_right_1 (a b c : ℕ) (h : a ≤ b) : a + c ≤ b + c :=
  Nat.add_le_add_right h c

theorem two_mul_eq_add_self_1 (n : ℕ) : 2 * n = n + n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Nat.mul_succ, ih]
    rw [Nat.add_succ, Nat.succ_add]

  theorem two_mul_eq_add_self_2 (n : ℕ) : 2 * n = n + n := by
  induction n with
  | zero => rfl  -- base case: 2 * 0 = 0 + 0 simplifies to 0 = 0
  | succ n ih =>
    rw [Nat.mul_succ]  -- changes 2 * (n+1) to 2 * n + 2
    rw [ih]            -- replaces 2 * n with n + n using induction hypothesis
    rw [Nat.add_succ, Nat.succ_add]  -- rearranges n + n + 2 to (n + 1) + (n + 1)
    rfl

--LLM input:
--Local LLM
theorem Nat.add_self_1 : ∀ n : ℕ, n + n = 2 * n := by
  -- Introduce the variable `n` which belongs to the type `ℕ`.
  intro n
  -- Use induction on `n` to prove the statement for all natural numbers.
  induction n with
  | zero =>
    -- Base case: When `n = 0`, we need to show `0 + 0 = 2 * 0`.
    simp [Nat.mul_zero] -- Simplify using the property that `2 * 0 = 0`.
  | succ n ih =>
    -- Inductive step: Assume the statement holds for `n`, i.e., `n + n = 2 * n`.
    cases n with
    | zero =>
      -- If `n = 0`, we need to show `0 + 0 = 2 * 0`, which is already simplified.
      simp [Nat.mul_zero] at ih ⊢ -- This line ensures that the inductive hypothesis holds for this case.
    | succ n =>
      -- For `n = k + 1`, use the inductive hypothesis `ih` to prove the statement.
      simp_all [Nat.mul_succ, Nat.add_assoc] -- Simplify using the properties of multiplication and addition.
      --<;> linarith

-- Website LLM
theorem Nat.add_self : ∀ n : ℕ, n + n = 2 * n := by
  intro n
  induction n with
  | zero =>
    -- Base case: n = 0
    simp [Nat.mul_zero]  -- Simplifies 2 * 0 to 0, confirming 0 + 0 = 0.
  | succ n ih =>
    -- Inductive step: Assume n + n = 2 * n (ih), prove for n + 1.
    simp_all [Nat.mul_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    -- Simplifies using multiplication by successor, associativity, and commutativity of addition.
    --<;> linarith  -- Confirms the equality using linear arithmetic.

--Trigonometry
example : sin (π / 2) = 1 := by norm_num
example : cos (π / 2) = 0 := by norm_num

theorem pythagorean_identity (a b c : ℕ) (h : a^2 + b^2 = c^2) : a^2 + b^2 = c^2 := by
  exact h

theorem circle_identity (x : ℝ) : sin x ^ 2 + cos x ^ 2 = 1 := by
  exact Real.sin_sq_add_cos_sq x

--tan(x)
theorem definition_of_tan (x : ℝ) : tan x = sin x / cos x :=
  Real.tan_eq_sin_div_cos x

--cot(x)
theorem definition_of_cot (x : ℝ) : cot x = cos x / sin x :=
  Real.cot_eq_cos_div_sin x

--csc(x)
noncomputable def csc (x : ℝ) : ℝ := 1 / sin x

theorem definition_of_csc (x : ℝ) : csc x =  1/ sin x :=
  rfl

--sec(x)
noncomputable def sec (x : ℝ) : ℝ := 1 / cos x
theorem definition_of_sec (x : ℝ) : sec x =  1/ cos x :=
  rfl

--sin(2x)=2sin(x)cos(x)。
theorem sin_double (x : ℝ) : sin (2 * x) = 2 * sin x * cos x :=
  Real.sin_two_mul x

--cos(2x)=cos^2(x) - sin^2(x)
theorem cos_double_alt (x : ℝ) : cos (2 * x) = cos x ^ 2 - sin x ^ 2 := by
  -- Use the identity: cos(2x) = 2 * cos^2(x) - 1
  rw [cos_two_mul]
  -- And recall: 1 = sin^2(x) + cos^2(x)
  rw [←sin_sq_add_cos_sq x]
  ring

-- Defining x and y in terms of r and theta

--variable (r θ : ℝ)

-- Define x = r * cos(θ)
--def x_rcos : ℝ := r * Real.cos θ

-- Define y = r * sin(θ)
--def y_rsin : ℝ := r * Real.sin θ

--#check x_rsin -- x : ℝ → ℝ → ℝ
--#check y_rcos -- y : ℝ → ℝ → ℝ
