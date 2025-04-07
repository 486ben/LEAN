
-- Definition and Theorem's name can't be the same name.
def main1 : IO Unit :=
  IO.println "Hello, world!"

def main2 : IO Unit :=
  IO.println "UCSC Master Thesis"

#eval main1
#eval main2

-- Another way to code
def main : IO Unit := do
  IO.println "Hello, world!"
  IO.println "UCSC Master Thesis"

#eval main

theorem implication_trans (P Q R : Prop)
  (h₁ : P → Q) (h₂ : Q → R) (hp : P) : R :=
by
  apply h₂  -- 我们想用 h₂ : Q → R
  apply h₁  -- 只要我们能提供 Q，我们就能从 h₁ : P → Q 得到它
  exact hp  -- 最后用 hp : P 得到 Q

theorem test (p q : Prop) --number
(hp : p)
(hq : q)
: p ∧ q ∧ p :=
  by apply And.intro
     exact hp
     apply And.intro
     exact hq
     exact hp
#print test


#eval Lean.versionString
