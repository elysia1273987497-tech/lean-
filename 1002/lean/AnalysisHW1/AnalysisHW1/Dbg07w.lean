import Mathlib

namespace Dbg07w

-- 只测这一条
example {a b : ℝ} (h : 1 < b - a) : (⌊b⌋ : ℝ) < b := by
  by_contra hc
  push_neg at hc
  -- hc : b ≤ ⌊b⌋
  have hb : b - 1 ≤ a := by linarith
  refine absurd ?_ (not_le.mpr h)
  -- 需证 `b - a ≤ 1`
  linarith

-- 另一写法
example {a b : ℝ} (h : 1 < b - a) : (⌊b⌋ : ℝ) < b := by
  by_contra hc
  push_neg at hc
  have hle : (⌊b⌋ : ℝ) ≤ b := Int.floor_le b
  have hb_eq : b = (⌊b⌋ : ℝ) := le_antisymm hc hle
  have : b - 1 < a := by linarith
  linarith

end Dbg07w
