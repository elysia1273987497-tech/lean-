import Mathlib

namespace Dbg07z

-- A: b*n < floor(n*b) + 1 到底能不能证
example {b : ℝ} {n : ℕ} :
    b * (n : ℝ) < (⌊(n : ℝ) * b⌋ : ℝ) + 1 := by
  have hfl : (n : ℝ) * b < (⌊(n : ℝ) * b⌋ : ℝ) + 1 := Int.lt_floor_add_one _
  have hfl' : b * (n : ℝ) < (⌊(n : ℝ) * b⌋ : ℝ) + 1 := by
    rw [mul_comm]; exact hfl
  exact hfl'

-- B: 完整的存在整数断言
example {a b : ℝ} (h : 1 < b - a) :
    ∃ m : ℤ, a < (m : ℝ) ∧ (m : ℝ) < b := by
  refine ⟨⌊b⌋, ?_, ?_⟩
  · by_contra hcon
    push_neg at hcon
    have hfl : b < (⌊b⌋ : ℝ) + 1 := Int.lt_floor_add_one b
    linarith
  · by_contra hcon
    push_neg at hcon
    have hfl : b < (⌊b⌋ : ℝ) + 1 := Int.lt_floor_add_one b
    have hle : (⌊b⌋ : ℝ) ≤ b := Int.floor_le b
    linarith

-- C: 有理数 * √2 无理
example {c : ℚ} (hc : c ≠ 0) : Irrational ((c : ℝ) * Real.sqrt 2) := by
  intro hmem
  obtain ⟨s, hs⟩ := hmem
  have hcR : (c : ℝ) ≠ 0 := by exact_mod_cast hc
  have hval : Real.sqrt 2 = (s : ℝ) / (c : ℝ) := by
    rw [eq_div_iff hcR]
    exact hs.symm
  have hcast : (((s / c : ℚ) : ℝ)) = (s : ℝ) / (c : ℝ) := by push_cast; ring
  exact irrational_sqrt_two ⟨s / c, by rw [hcast, hval]⟩

end Dbg07z
