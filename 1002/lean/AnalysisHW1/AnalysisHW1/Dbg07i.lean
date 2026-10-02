import Mathlib

namespace Dbg07i

-- 测 B': a < f n 的推导，绕开 nlinarith
example {a b : ℝ} (hab : a < b) (n : ℕ) (fn : ℝ)
    (h1 : b - (b - a) / ((n : ℝ) + 1) < fn) : a < fn := by
  have hden : (1 : ℝ) ≤ (n : ℝ) + 1 := by
    have : (0 : ℝ) ≤ n := by positivity
    linarith
  have hba : (0 : ℝ) < b - a := by linarith
  have hfrac : (b - a) / ((n : ℝ) + 1) ≤ b - a := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < (n : ℝ) + 1)]
    nlinarith
  have hbase : a = b - (b - a) := by ring
  linarith [h1, hfrac, hbase]

-- 测 C': 正确的矛盾形状
example {lo hi f : ℝ} (h1 : hi < f) (h2 : f < lo) (h3 : lo ≤ hi) : False := by linarith

-- 测 D': 带除法的正确矛盾形状
example {a b : ℝ} (m n : ℕ) (fn : ℝ)
    (h1 : b - (b - a) / ((n : ℝ) + 1) < fn)
    (h2 : fn < b - (b - a) / ((m : ℝ) + 1))
    (h3 : b - (b - a) / ((n : ℝ) + 1) ≤ b - (b - a) / ((m : ℝ) + 1)) : False := by
  linarith

end Dbg07i
