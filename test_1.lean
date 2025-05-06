--import Mathlib
import Mathlib.Algebra.Group.Basic

-- 导入群论基础
import Mathlib.Algebra.Group.Defs

import Mathlib.Data.Nat.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Tactic.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

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

--Even number
