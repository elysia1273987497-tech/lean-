import Mathlib

namespace Dbg01f

-- 只测「反向重写」问题：直接构造，不用 rw
example (a b : ℤ) : (a ^ 2 = b ^ 2) ↔ (b = a ∨ b = -a) := by
  constructor
  · intro h
    have h2 : a = b ∨ a = -b := by
      have hfac : a ^ 2 - b ^ 2 = (a - b) * (a + b) := by ring
      rw [← sub_eq_zero, hfac, mul_eq_zero, sub_eq_zero, add_eq_zero_iff_eq_neg] at h
      exact h
    rcases h2 with h2 | h2
    · exact Or.inl h2.symm
    · exact Or.inr (by rw [h2]; ring)
  · intro h
    rcases h with h | h
    · rw [h]; ring
    · rw [h]; ring

-- 四类加法情形，逐个用 subst + ring 检验
example {a b c d : ℤ} (h : a = b) (h' : c = d) : (a + c) ^ 2 = (b + d) ^ 2 := by
  subst h; subst h'; ring

example {a b c d : ℤ} (h : a = b) (h' : c = -d) : (a + c) ^ 2 = (b + d) ^ 2 := by
  subst h; subst h'; ring

example {a b c d : ℤ} (h : a = -b) (h' : c = d) : (a + c) ^ 2 = (b + d) ^ 2 := by
  subst h; subst h'; ring

example {a b c d : ℤ} (h : a = -b) (h' : c = -d) : (a + c) ^ 2 = (b + d) ^ 2 := by
  subst h; subst h'; ring

end Dbg01f
