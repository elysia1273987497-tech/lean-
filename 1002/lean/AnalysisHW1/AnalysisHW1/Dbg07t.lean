import Mathlib

namespace Dbg07t

-- 正确的第二支证明：hc : b ≤ ⌊b⌋ 与 h : 1 < b - a 矛盾
example {a b : ℝ} (h : 1 < b - a) (hc : b ≤ (⌊b⌋ : ℝ)) : False := by
  have hle : (⌊b⌋ : ℝ) ≤ b := Int.floor_le b
  -- 于是 `b = ⌊b⌋`
  have hb_eq : b = (⌊b⌋ : ℝ) := le_antisymm hc hle
  -- `b - 1 < a`（由 h）
  have h1 : b - 1 < a := by linarith
  -- `a ≤ b - 1`（由 hb_eq 与 ⌊b⌋ ≤ b）
  have h2 : a ≤ b - 1 := by linarith
  linarith

-- 完整引理
example {a b : ℝ} (h : 1 < b - a) :
    ∃ m : ℤ, a < (m : ℝ) ∧ (m : ℝ) < b := by
  have hgt : a < (⌊b⌋ : ℝ) := by
    by_contra hc
    push_neg at hc
    have hfl : b < (⌊b⌋ : ℝ) + 1 := Int.lt_floor_add_one b
    linarith
  refine ⟨⌊b⌋, hgt, ?_⟩
  by_contra hc
  push_neg at hc
  have hle : (⌊b⌋ : ℝ) ≤ b := Int.floor_le b
  have hb_eq : b = (⌊b⌋ : ℝ) := le_antisymm hc hle
  have h1 : b - 1 < a := by linarith
  linarith

end Dbg07t
