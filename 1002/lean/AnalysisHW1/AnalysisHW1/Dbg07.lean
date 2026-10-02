import Mathlib

namespace Dbg07

-- 测 1: a < ⌊b⌋ 能否推出 ⌊b⌋ ≤ a + 1
example {a b : ℝ} (hgt : a < (⌊b⌋ : ℝ)) : (⌊b⌋ : ℝ) ≤ a + 1 := by linarith

example {a b : ℝ} (hgt : a < (⌊b⌋ : ℝ)) : (⌊b⌋ : ℝ) ≤ a + 1 := by
  apply Int.le_floor.mpr
  push_cast
  linarith

-- 测 2: exists_nat_gt 的否定分支
example {t : ℝ} (ht : 0 < t) : True := by
  obtain ⟨n, hn⟩ := exists_nat_gt t
  have hnpos : 0 < n := by
    by_contra h
    push_neg at h
    have h0 : n = 0 := Nat.le_zero.mp h
    subst h0
    norm_num at hn
  trivial

-- 测 3: a < f n 的推导
example {a b : ℝ} (hab : a < b) (n : ℕ) (fn : ℝ)
    (h1 : b - (b - a) / ((n : ℝ) + 1) < fn) (h2 : fn < b) : a < fn := by
  have hb : (0 : ℝ) < b - a := by linarith
  have hfrac : (b - a) / ((n : ℝ) + 1) < b - a := by
    have hlt : (1 : ℝ) < (n : ℝ) + 1 := by
      have : (0 : ℝ) ≤ n := by positivity
      linarith
    rw [div_lt_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 1)]
    nlinarith
  linarith

end Dbg07
