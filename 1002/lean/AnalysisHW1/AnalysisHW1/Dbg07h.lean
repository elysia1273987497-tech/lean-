import Mathlib

namespace Dbg07h

-- 测 A: b*n < floor(n*b) + 1 的两条链
example {b : ℝ} {n : ℕ} (hn : 0 < n) :
    b * (n : ℝ) < (⌊(n : ℝ) * b⌋ : ℝ) + 1 := by
  have hfl : (n : ℝ) * b < (⌊(n : ℝ) * b⌋ : ℝ) + 1 := Int.lt_floor_add_one _
  have hfl' : b * (n : ℝ) < (⌊(n : ℝ) * b⌋ : ℝ) + 1 := by
    rw [mul_comm]; exact hfl
  exact hfl'

-- 测 B: a < f n 的完整推导
example {a b : ℝ} (hab : a < b) (n : ℕ) (fn : ℝ)
    (h1 : b - (b - a) / ((n : ℝ) + 1) < fn) : a < fn := by
  have hfrac : (b - a) / ((n : ℝ) + 1) < b - a := by
    have hlt : (1 : ℝ) < (n : ℝ) + 1 := by
      have : (0 : ℝ) ≤ n := by positivity
      linarith
    rw [div_lt_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 1)]
    nlinarith
  have hbase : a = b - (b - a) := by ring
  linarith [h1, hfrac, hbase]

-- 测 C: 单射的矛盾（用抽象符号）
example {x y u v : ℝ} (h1 : x < u) (h2 : y < u) (h3 : x < y) : False := by linarith

-- 测 D: 带除法的单射矛盾
example {a b : ℝ} (hab : a < b) (m n : ℕ) (hmn : m < n) (fn : ℝ)
    (h1 : b - (b - a) / ((m : ℝ) + 1) < fn)
    (h2 : b - (b - a) / ((n : ℝ) + 1) < fn)
    (h3 : b - (b - a) / ((m : ℝ) + 1) < b - (b - a) / ((n : ℝ) + 1)) : False := by
  linarith

end Dbg07h
