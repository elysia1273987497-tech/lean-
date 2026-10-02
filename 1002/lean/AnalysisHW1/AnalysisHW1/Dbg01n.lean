import Mathlib

namespace Dbg01n

def R (a b : ℤ) : Prop := a ^ 2 = b ^ 2

def WellDefined (f : ℤ → ℤ → ℤ) : Prop :=
  ∀ a b c d : ℤ, R a b → R c d → R (f a c) (f b d)

-- 最朴素写法：直接 exact，让 Lean 自己统一
example (h : WellDefined (· + ·)) : False := by
  have hbad : R ((1 : ℤ) + (-1)) (1 + 1) := h 1 1 (-1) (-1) rfl rfl
  unfold R at hbad
  norm_num at hbad

-- 用 show 指定目标形状
example (h : WellDefined (· + ·)) : False := by
  have hbad : (1 : ℤ) + (-1) = 1 + 1 → False := by
    intro _
    exact (by unfold R at *; norm_num : ¬ R ((1 : ℤ) + (-1)) (1 + 1)) (h 1 1 (-1) (-1) rfl rfl)
  exact hbad rfl

-- 完全显式：先固定 a b c d
example (h : WellDefined (· + ·)) : False := by
  obtain ⟨a, b, c, d, ha, hc⟩ : ∃ a b c d : ℤ, R a b ∧ R c d ∧ ¬ R (a + c) (b + d) :=
    ⟨1, 1, -1, -1, rfl, rfl, by unfold R; norm_num⟩
  exact hc (h a b c d ha hc.left)

end Dbg01n
