import Mathlib

namespace Dbg01m

def R (a b : ℤ) : Prop := a ^ 2 = b ^ 2

def WellDefined (f : ℤ → ℤ → ℤ) : Prop :=
  ∀ a b c d : ℤ, R a b → R c d → R (f a c) (f b d)

-- 逐行拆分，找出 h 应用的真正类型
example (h : WellDefined (· + ·)) : False := by
  have hR1 : R (1 : ℤ) 1 := rfl
  have hR2 : R (-1 : ℤ) (-1) := rfl
  have step : R ((fun x1 x2 : ℤ => x1 + x2) 1 (-1)) ((fun x1 x2 : ℤ => x1 + x2) 1 1) :=
    h 1 1 (-1) (-1) hR1 hR2
  have hbad : R (0 : ℤ) 2 := step
  unfold R at hbad
  norm_num at hbad

end Dbg01m
