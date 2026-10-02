import Mathlib

namespace Dbg07e

-- 试：n = ⌊1/(b-a)⌋ + 1 使 n(b-a) > 1，再在 (na, nb) 中取整数
example {a b : ℝ} (hab : a < b) : ∃ q : ℚ, a < (q : ℝ) ∧ (q : ℝ) < b := by
  have hb : 0 < b - a := by linarith
  -- 取自然数 n 使 1 < n * (b - a)（等价于 1/(b-a) < n）
  obtain ⟨k, hk⟩ := exists_nat_gt (1 / (b - a))
  have hnk : 1 < (k : ℝ) * (b - a) := by
    rw [div_lt_iff₀ hb] at hk
    linarith
  have hkpos : 0 < k := by
    by_contra h
    push_neg at h
    have h0 : k = 0 := Nat.le_zero.mp h
    subst h0
    norm_num at hnk
  have hk' : (0 : ℝ) < k := by exact_mod_cast hkpos
  -- 在 (k*a, k*b) 中取整数 m：用 ⌊k*b⌋
  have hlt : (k : ℝ) * a < (⌊(k : ℝ) * b⌋ : ℝ) := by
    have hfl : (k : ℝ) * b < (⌊(k : ℝ) * b⌋ : ℝ) + 1 := Int.lt_floor_add_one _
    by_contra hc
    push_neg at hc
    -- hc : ⌊k*b⌋ ≤ k*a
    -- 与 hfl 一起给 k*b < k*a + 1，即 k*(b-a) < 1，与 hnk 矛盾
    linarith
  have hlt2 : (⌊(k : ℝ) * b⌋ : ℝ) < (k : ℝ) * b := by
    by_contra hc
    push_neg at hc
    -- hc : k*b ≤ ⌊k*b⌋，而 ⌊k*b⌋ ≤ k*b，故相等
    have hle : (⌊(k : ℝ) * b⌋ : ℝ) ≤ (k : ℝ) * b := Int.floor_le _
    have heq : (⌊(k : ℝ) * b⌋ : ℝ) = (k : ℝ) * b := le_antisymm hc hle
    -- 于是 k*b 是整数；这本身不矛盾。改取 ⌊k*b⌋ - 1？
    sorry
  sorry

end Dbg07e
