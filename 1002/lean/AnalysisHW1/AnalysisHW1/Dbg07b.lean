import Mathlib

namespace Dbg07b

-- 测 1: 先问 Lean 一个更基本的问题 —— a+1 < ⌊b⌋ 与 h 到底矛不矛盾
example {a b : ℝ} (h : 1 < b - a) (hc : a + 1 < (⌊b⌋ : ℝ)) : True := by
  have hb : (⌊b⌋ : ℝ) ≤ b := Int.floor_le b
  -- 这里 `a + 1 < ⌊b⌋ ≤ b` 只是重复了 `h`，无矛盾
  trivial

-- 正确的思路：⌊b⌋ ≤ a+1 的反面配合 h 需要 b 本身参与
-- 直接用 Real 的取整性质：⌊b⌋ - 1 < a（由 h 与 ⌊b⌋ ≥ b-1 推出）
example {a b : ℝ} (h : 1 < b - a) : (⌊b⌋ : ℝ) - 1 < a := by
  have hle : b - 1 < (⌊b⌋ : ℝ) := by
    have hfl : b < (⌊b⌋ : ℝ) + 1 := Int.lt_floor_add_one b
    linarith
  linarith

-- 测 2: t < 0 与 0 < t 矛盾
example {t : ℝ} (ht : 0 < t) : True := by
  obtain ⟨n, hn⟩ := exists_nat_gt t
  have hnpos : 0 < n := by
    by_contra h
    push_neg at h
    have h0 : n = 0 := Nat.le_zero.mp h
    subst h0
    norm_num at hn
    linarith
  trivial

-- 测 3: a < f n
example {a b : ℝ} (hab : a < b) (n : ℕ) (fn : ℝ)
    (h1 : b - (b - a) / ((n : ℝ) + 1) < fn) : a < fn := by
  have hb : (0 : ℝ) < b - a := by linarith
  have hden : (1 : ℝ) ≤ (n : ℝ) + 1 := by
    have : (0 : ℝ) ≤ n := by positivity
    linarith
  have hfrac : (b - a) / ((n : ℝ) + 1) ≤ b - a := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 1)]
    nlinarith
  linarith

end Dbg07b
