import Mathlib

namespace Dbg01j

def R (a b : ℤ) : Prop := a ^ 2 = b ^ 2

def WellDefined (f : ℤ → ℤ → ℤ) : Prop :=
  ∀ a b c d : ℤ, R a b → R c d → R (f a c) (f b d)

-- B: 用具体反例证 ¬ WellDefined，检查 R 两边的具体项
example : ¬ R (1 + 1) ((-1) + (-1)) := by unfold R; norm_num

example : ¬ WellDefined (· + ·) := by
  intro h
  have h2 : R (1 + 1) ((-1) + (-1)) :=
    h 1 (-1) 1 (-1) (by unfold R; norm_num) (by unfold R; norm_num)
  exact (by unfold R; norm_num : ¬ R (1 + 1) ((-1) + (-1))) h2

-- C: class_eq 的正确写法（用 h.symm 转换）
theorem sq_eq_sq_iff (a b : ℤ) : a ^ 2 = b ^ 2 ↔ (a = b ∨ a = -b) := by
  have hfac : a ^ 2 - b ^ 2 = (a - b) * (a + b) := by ring
  rw [← sub_eq_zero, hfac, mul_eq_zero, sub_eq_zero, add_eq_zero_iff_eq_neg]

example (a : ℤ) : {b | R a b} = ({a, -a} : Set ℤ) := by
  ext b
  simp only [R, Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · intro h
    rcases (sq_eq_sq_iff b a).mp h.symm with h' | h'
    · exact Or.inl h'.symm
    · exact Or.inr (by rw [h']; ring)
  · intro h
    rcases h with h | h
    · rw [h]
    · rw [h]; ring

end Dbg01j
