import Mathlib

namespace Dbg01i

def R (a b : ℤ) : Prop := a ^ 2 = b ^ 2

-- A: 检查 (2:ℤ)^2 = (-2:ℤ)^2 的可证性
example : (2 : ℤ) ^ 2 = (-2 : ℤ) ^ 2 := by norm_num
example : R (1 + 1) ((-1) + (-1)) := by norm_num [R]
example : R (1 + 1) ((-1) + (-1)) := by unfold R; norm_num

-- B: 用具体反例证 ¬ WellDefined
def WellDefined (f : ℤ → ℤ → ℤ) : Prop :=
  ∀ a b c d : ℤ, R a b → R c d → R (f a c) (f b d)

example : ¬ WellDefined (· + ·) := by
  intro h
  have h2 : R (1 + 1) ((-1) + (-1)) :=
    h 1 (-1) 1 (-1) (by norm_num [R]) (by norm_num [R])
  have : ¬ R (1 + 1) ((-1) + (-1)) := by unfold R; norm_num
  exact this h2

-- C: class_eq 的正确写法
theorem sq_eq_sq_iff (a b : ℤ) : a ^ 2 = b ^ 2 ↔ (a = b ∨ a = -b) := by
  have hfac : a ^ 2 - b ^ 2 = (a - b) * (a + b) := by ring
  rw [← sub_eq_zero, hfac, mul_eq_zero, sub_eq_zero, add_eq_zero_iff_eq_neg]
  tauto

example (a : ℤ) : {b | R a b} = ({a, -a} : Set ℤ) := by
  ext b
  simp only [R, Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · intro h
    rcases (sq_eq_sq_iff b a).mp h with h' | h'
    · exact Or.inl h'.symm
    · exact Or.inr (by rw [h']; ring)
  · intro h
    rcases h with h | h
    · rw [h]
    · rw [h]; ring

end Dbg01i
