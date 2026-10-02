import Mathlib

namespace Dbg07y

-- 整数存在性（用 ⌊b⌋）
example {a b : ℝ} (h : 1 < b - a) :
    ∃ m : ℤ, a < (m : ℝ) ∧ (m : ℝ) < b := by
  have hgt : a < (⌊b⌋ : ℝ) := by
    by_contra hc
    push_neg at hc
    have hfl : b < (⌊b⌋ : ℝ) + 1 := Int.lt_floor_add_one b
    linarith
  have hlt : (⌊b⌋ : ℝ) < b := by
    by_contra hc
    push_neg at hc
    have hb : b - 1 < a := by linarith
    linarith
  exact ⟨⌊b⌋, hgt, hlt⟩

-- 有理数乘 √2
example {c : ℚ} (hc : c ≠ 0) : Irrational ((c : ℝ) * Real.sqrt 2) := by
  intro hmem
  obtain ⟨s, hs⟩ := hmem
  have hcR : (c : ℝ) ≠ 0 := by exact_mod_cast hc
  have hs' : Real.sqrt 2 * (c : ℝ) = (s : ℝ) := by
    rw [mul_comm]; exact hs.symm
  have hval : Real.sqrt 2 = (s : ℝ) / (c : ℝ) := by
    rw [eq_div_iff hcR]; exact hs'
  have hcast : (((s / c : ℚ) : ℝ)) = (s : ℝ) / (c : ℝ) := by push_cast; ring
  exact irrational_sqrt_two ⟨s / c, by rw [hcast, hval]⟩

end Dbg07y
