import Mathlib

namespace Dbg11b

-- hφ0 片段
example {x a : ℝ} {n : ℕ} (hxpos : 0 < x) (hgap : 0 < a - x ^ n) :
    let C : ℝ := (n : ℝ) * (1 + 1) ^ (n - 1) + 1
    0 < min (min (x / 2) 1) ((a - x ^ n) / C) := by
  intro C
  have hCpos : 0 < C := by positivity
  exact lt_min (lt_min (by linarith) one_pos) (div_pos hgap hCpos)

-- hφgap 片段
example {x a C φ : ℝ} (hCpos : 0 < C) (hφdef : φ = min (min (x / 2) 1) ((a - x ^ n) / C)) :
    C * φ ≤ C * ((a - x ^ n) / C) := by
  rw [hφdef]
  exact mul_le_mul_of_nonneg_left (min_le_right _ _) hCpos.le

end Dbg11b
