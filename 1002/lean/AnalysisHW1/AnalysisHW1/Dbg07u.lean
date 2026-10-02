import Mathlib

namespace Dbg07u

-- 整数存在性：m = ⌊b⌋
example {a b : ℝ} (h : 1 < b - a) :
    ∃ m : ℤ, a < (m : ℝ) ∧ (m : ℝ) < b := by
  refine ⟨⌊b⌋, ?_, ?_⟩
  · by_contra hc
    push_neg at hc
    have hfl : b < (⌊b⌋ : ℝ) + 1 := Int.lt_floor_add_one b
    linarith
  · by_contra hc
    push_neg at hc
    -- hc : b ≤ ⌊b⌋，故 ⌊b⌋ = b
    have hle : (⌊b⌋ : ℝ) ≤ b := Int.floor_le b
    have hb_eq : b = (⌊b⌋ : ℝ) := le_antisymm hc hle
    -- 由 `1 < b - a` 得 `b - 1 < a`
    have hba : b - 1 < a := by linarith
    -- 但 `b = ⌊b⌋` 与 `a < ⌊b⌋`（第一支已证）不冲突……
    -- 真正的矛盾：`1 < b - a` 与 `a < b`（由 hb_eq 与 a < ⌊b⌋ = b）
    have hab : a < b := by
      have : a < (⌊b⌋ : ℝ) := by
        by_contra h2
        push_neg at h2
        have hfl : b < (⌊b⌋ : ℝ) + 1 := Int.lt_floor_add_one b
        linarith
      linarith
    linarith

end Dbg07u
