import Mathlib

namespace Dbg07f

-- 关键：1 < b - a ⟹ a < ⌊b⌋
example {a b : ℝ} (h : 1 < b - a) : a < (⌊b⌋ : ℝ) := by
  by_contra hc
  push_neg at hc
  have hfl : b < (⌊b⌋ : ℝ) + 1 := Int.lt_floor_add_one b
  linarith

-- 见证：m = ⌊b⌋，第二条件用 hle 直接给（不需要严格）
example {a b : ℝ} (h : 1 < b - a) : ∃ m : ℤ, a < (m : ℝ) ∧ (m : ℝ) ≤ b := by
  refine ⟨⌊b⌋, ?_, Int.floor_le b⟩
  by_contra hc
  push_neg at hc
  have hfl : b < (⌊b⌋ : ℝ) + 1 := Int.lt_floor_add_one b
  linarith

-- 严格版：若 b 不是整数，则 ⌊b⌋ < b
example {b : ℝ} (hb : ∀ m : ℤ, (m : ℝ) ≠ b) : (⌊b⌋ : ℝ) < b := by
  by_contra hc
  push_neg at hc
  exact hb ⌊b⌋ (le_antisymm hc (Int.floor_le b))

end Dbg07f
