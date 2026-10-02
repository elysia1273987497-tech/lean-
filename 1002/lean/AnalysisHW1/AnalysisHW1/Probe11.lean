import Mathlib

namespace Probe11

-- P11 需要：sSup 的刻画、Real 上的幂
#check @Real.sq_sqrt
#check @sq_le_sq
#check @pow_le_pow_left₀
#check @pow_lt_pow_left₀
#check @sub_le_sub_left
#check @le_csSup
#check @csSup_le
#check @lt_of_lt_of_le
#check @Finset.sum_range_succ
#check @geom_sum_mul
#check @mul_le_mul_of_nonneg_left
#check @le_of_forall_pos_le_add

-- 多项式恒等式 u^n - v^n = (u-v) * sum
example (u v : ℝ) (n : ℕ) :
    u ^ (n + 1) - v ^ (n + 1) = (u - v) * ∑ j ∈ Finset.range (n + 1), u ^ (n - j) * v ^ j := by
  rw [geom_sum_mul]
  ring

end Probe11
