import Mathlib

namespace Dbg02

-- 1) IsPartialOrder 的真正字段
example : IsPartialOrder ℕ (· ∣ ·) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a; exact dvd_refl a
  · intro a b c hab hbc; exact dvd_trans hab hbc
  · intro a b hab hba; exact Nat.dvd_antisymm hab hba

-- 2) 全序的直接写法
example : ¬ (∀ a b : ℕ, a ∣ b ∨ b ∣ a) := by
  intro h
  rcases h 4 6 with h46 | h64
  · norm_num at h46
  · norm_num at h64

-- 3) 集合包含的反方向
def R (a b : ℤ) : Prop := a ^ 2 = b ^ 2

example (a : ℤ) : {b | R a b} ⊆ ({a, -a} : Set ℤ) := by
  intro b h
  simp only [Set.mem_setOf_eq, R] at h
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  have h' : b = a ∨ b = -a := by
    have hfac : b ^ 2 - a ^ 2 = (b - a) * (b + a) := by ring
    rw [← sub_eq_zero, hfac, mul_eq_zero, sub_eq_zero, add_eq_zero_iff_eq_neg] at h
    exact h
  exact h'

end Dbg02
