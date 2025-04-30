import Mathlib.Algebra.Group.Basic

-- 导入群论基础
import Mathlib.Algebra.Group.Defs

import Mathlib.Topology.Basic

-- Definition and Theorem's name can't be the same name.
def main1 : IO Unit :=
  IO.println "Hello, world!"

def main2 : IO Unit :=
  IO.println "UCSC Master Thesis"

#eval main1
#eval main2

--another way to print
#eval "ZhiBin" ++ " " ++ "Master" ++ " " ++ "Thesis"
-- Another way to code
def main : IO Unit := do
  IO.println "Hello, world!"
  IO.println "UCSC Master Thesis"

#eval main


--CalculationWWW
def x_1 := 10

#eval x_1 + 3
#eval x_1 - 9

-- define a definition of double
def double(x : Int) := 2 * x

#eval double 10

#check double

--example
example : double 4 = 8 := rfl


--Theorem represent
theorem implication_trans (P Q R : Prop)
  (h₁ : P → Q) (h₂ : Q → R) (hp : P) : R :=
by
  apply h₂  -- 我们想用 h₂ : Q → R
  apply h₁  -- 只要我们能提供 Q，我们就能从 h₁ : P → Q 得到它
  exact hp  -- 最后用 hp : P 得到 Q

--print out some test
#print implication_trans

theorem test (p q : Prop) --number
(hp : p)
(hq : q)
: p ∧ q ∧ p :=
  by apply And.intro
     exact hp
     apply And.intro
     exact hq
     exact hp

--print out some test
#print test

--SOme example
--example : <statement> := <proof>
--example : <statement> :=
--by
  --<tactic steps>

--correct example
example : 2 + 2 = 4 :=
by
  rfl   -- reflexivity (both sides reduce to 4)

--correct example
example : 2 + 5 = 8 :=
by
  rfl   -- reflexivity (both sides reduce to 4)

--
def twice (f : Nat → Nat) (a : Nat) := f (f a)
-- → is \ + to
-- is a function that takes a natural number and returns a natural number.
-- a : Nat is a natural number.
#print twice
#check twice
--twice (f : Nat → Nat) (a : Nat) : Na

--double do the f * a = f (f a)
#eval twice (fun x => x + 2) 10 --input x = 10
--twice f a = f (f a)
--→ f = (fun x => x + 2)
--→ f(f(10)) = f(12) = 14


#eval twice ( · + 5) 10
-- first 10 + 5 = 15
-- second 15 + 5 = 20
--The dot · is type \ + .

#eval twice ( · - 2) 10
-- first 10 - 2 = 8
-- second 8 - 2 = 6
--The dot · is type \ + .

--check natural number
#check 2 = 2
#check 0
#check Nat
#check Type
#check Type 1

--example
example : Prop = Sort 0 := rfl
example : Type = Sort 1 := rfl
example : Type 1 = Sort 2 := rfl

--lemma
--lemma even_add_one {n : ℕ} : even n → odd (n + 1) := sorry

variable (a b c d e : Nat)
variable (h1 : a = b)
variable (h2 : b = c + 1)
variable (h3 : c = d)
variable (h4 : e = 1 + d)

--theorem T : a = e := by
  -- 使用等式传递组合证明
  --rw [h1, h2, h3, Nat.add_comm]
  -- 自动验证最终等式
  --<;> rfl

-- 验证群定义
#check Group
-- 输出: Group : Type u → Type u

-- 正确Lean函数定义
def foo (x : Nat) : Nat :=
  x + 1

-- 函数调用示例
#eval foo 1  -- 输出: 2

#check a = e
#check h1 = h1
--Version
#eval Lean.versionString


--Theorem compare to human written and LLM model

--Example if a = b, then b = a. Human Written:
example (a b : ℕ) (h : a = b) : b = a :=
  Eq.symm h

--LLM Written:
theorem if_a_eq_b_then_eq : ∀ a b : ℕ, a = b → b = a := by
  -- Introduce the variables `a` and `b`, and assume `h : a = b`.
  intro a b h
  -- Apply the symmetry of equality to get `b = a` from `a = b`.
  exact Eq.symm h
  -- Use `linarith` or `rfl` to confirm the equality.
  --<;> linarith
  -- The `<;>` operator chains tactics, applying each in sequence.
  -- Here, it applies `linarith` after `rw [eq.symm]`.
  -- However, since `a = b` directly implies `b = a`, we can use `rfl` for simplicity.
 --<;> rfl


----------------------------------------
-- 人类风格手工证明版本（使用结构归纳）
-- Human-style handwritten proof (using structural induction)
lemma one_mul_handwritten (n : ℕ) : 1 * n = n := by
  induction n with                -- 对 n 做归纳 / Do induction on n
  | zero =>                      -- 基础情况：n = 0 / Base case: n = 0
    rfl                          -- 1 * 0 = 0，根据乘法定义，直接成立 / Follows directly from definition
  | succ n ih =>                 -- 归纳情况：n = succ n / Inductive step: n = succ n
    simp [Nat.mul_succ, ih]      -- 使用乘法定义和归纳假设简化 / Use multiplication definition and induction hypothesis

-- English explanation:
-- `Nat.mul_succ` defines multiplication recursively: a * succ b = a * b + a
-- `simp` applies this and simplifies using the induction hypothesis `ih`

-- 中文解释：
-- Nat.mul_succ 是 Lean 中乘法定义：a * succ b = a * b + a
-- simp 会自动套用定义，然后使用归纳假设 ih 简化目标式

--LLM Written:
theorem leftIdentity : ∀ a : ℕ, 1 * a = a := by
  intro a                        -- Introduce `a` into the goal
  rw [Nat.one_mul]               -- Rewrite using the lemma `Nat.one_mul : 1 * a = a`
  --simp                           -- Simplify the goal, which is now trivially true (1 * a = a)
  -- The goal is now solved using `simp` since `1 * a = a` is directly simplified to `a`
  --rfl                            -- The proof is complete, the goal is trivially `a = a
