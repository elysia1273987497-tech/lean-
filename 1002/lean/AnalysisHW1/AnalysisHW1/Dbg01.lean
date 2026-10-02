import Mathlib

-- 调试文件：逐个隔离 Problem01 的四个错误
set_option autoImplicit false

namespace Dbg01

def R (a b : ℤ) : Prop := a ^ 2 = b ^ 2

theorem sq_eq_sq_iff (a b : ℤ) : a ^ 2 = b ^ 2 ↔ (a = b ∨ a = -b) := by
  have hfac : a ^ 2 - b ^ 2 = (a - b) * (a + b) := by ring
  rw [← sub_eq_zero, hfac, mul_eq_zero, sub_eq_zero, add_eq_zero_iff_eq_neg]
  tauto

-- 问题 1: Equivalence 构造子
theorem dbg_equiv : Equivalence R := by
  refine ⟨?_, ?_, ?_⟩
  · intro a; rfl
  · intro a b hab; exact hab.symm
  · intro a b c hab hbc; exact hab.trans hbc

-- 问题 2: 反向重写
theorem dbg_class (a : ℤ) : {b | R a b} = ({a, -a} : Set ℤ) := by
  ext b
  simp only [R, Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · intro h
    have h2 : b = a ∨ b = -a := (sq_eq_sq_iff b a).mp h
    tauto
  · intro h
    rcases h with h | h
    · exact h ▸ (sq_eq_sq_iff a a).mpr (Or.inl rfl)
    · exact (sq_eq_sq_iff b a).mpr (Or.inr h)

-- 问题 3: 良定义加法
theorem dbg_add_wd : ∀ a b c d : ℤ, R a b → R c d → R (a + c) (b + d) := by
  intro a b c d hab hcd
  rw [R] at hab hcd ⊢
  obtain h | h := (sq_eq_sq_iff a b).mp hab
  · obtain h' | h' := (sq_eq_sq_iff c d).mp hcd
    · rw [h, h']
    · rw [h, h']; ring
  · obtain h' | h' := (sq_eq_sq_iff c d).mp hcd
    · rw [h, h']; ring
    · rw [h, h']; ring

-- 问题 4: 乘法不良定义
theorem dbg_mul_not_wd : ¬ (∀ a b c d : ℤ, R a b → R c d → R (a * c) (b * d)) := by
  intro h
  have h5 : R (5 * 5) (5 * (-5)) :=
    h 5 5 5 (-5) (by decide) (by decide)
  rw [R] at h5
  norm_num at h5

end Dbg01
