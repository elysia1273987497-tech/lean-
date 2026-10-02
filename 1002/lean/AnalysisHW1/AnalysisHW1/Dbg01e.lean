import Mathlib

namespace Dbg01e

def R (a b : ℤ) : Prop := a ^ 2 = b ^ 2

-- 单独隔离「乘法不良定义」的收尾
theorem dbg_mul_not_wd : ¬ (∀ a b c d : ℤ, R a b → R c d → R (a * c) (b * d)) := by
  intro h
  have h5 : R (5 * 5) (5 * (-5)) :=
    h 5 5 5 (-5) (by norm_num [R]) (by norm_num [R])
  rw [R] at h5
  norm_num at h5
  exact h5

-- 另一种收尾：直接给反例
example : ¬ R (5 * 5) (5 * (-5)) → ¬ (∀ a b c d : ℤ, R a b → R c d → R (a * c) (b * d)) := by
  intro h25 h
  exact h25 (h 5 5 5 (-5) (by norm_num [R]) (by norm_num [R]))

end Dbg01e
