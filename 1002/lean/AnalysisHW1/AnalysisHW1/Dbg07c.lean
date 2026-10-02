import Mathlib

namespace Dbg07c

-- 目标：1 < b - a 时存在整数 m 使 a < m < b
-- 思路：m = ⌊b⌋，需要 a < ⌊b⌋ 与 ⌊b⌋ < b

-- 步骤 1: a < ⌊b⌋
example {a b : ℝ} (h : 1 < b - a) : a < (⌊b⌋ : ℝ) := by
  have hfl : b < (⌊b⌋ : ℝ) + 1 := Int.lt_floor_add_one b
  by_contra hc
  push_neg at hc
  linarith

-- 步骤 2: ⌊b⌋ < b，用反证 + 步骤 1
example {a b : ℝ} (h : 1 < b - a) : (⌊b⌋ : ℝ) < b := by
  have hgt : a < (⌊b⌋ : ℝ) := by
    have hfl : b < (⌊b⌋ : ℝ) + 1 := Int.lt_floor_add_one b
    by_contra hc
    push_neg at hc
    linarith
  by_contra hc
  push_neg at hc
  have hle : (⌊b⌋ : ℝ) ≤ b := Int.floor_le b
  -- hc : b ≤ ⌊b⌋，结合 hle 得 ⌊b⌋ = b；而 hgt 给 a < ⌊b⌋
  -- 由 h 得 b - 1 < a，于是 b - 1 < ⌊b⌋ = b
  have hb : b - 1 < a := by linarith
  linarith

-- 结论
example {a b : ℝ} (h : 1 < b - a) : ∃ m : ℤ, a < (m : ℝ) ∧ (m : ℝ) < b := by
  have hgt : a < (⌊b⌋ : ℝ) := by
    have hfl : b < (⌊b⌋ : ℝ) + 1 := Int.lt_floor_add_one b
    by_contra hc
    push_neg at hc
    linarith
  have hlt : (⌊b⌋ : ℝ) < b := by
    by_contra hc
    push_neg at hc
    have hb : b - 1 < a := by linarith
    linarith
  exact ⟨⌊b⌋, hgt, hlt⟩

end Dbg07c
