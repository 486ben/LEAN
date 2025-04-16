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
