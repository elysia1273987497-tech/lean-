import Mathlib

namespace Dbg02b

-- 1) IsPartialOrder 是类，不能直接用匿名构造子；改用 IsRefl/IsAntisymm/IsTrans 或直接陈述
example : IsRefl ℕ (· ∣ ·) := ⟨fun a => dvd_refl a⟩

example : IsTrans ℕ (· ∣ ·) := ⟨fun a b c hab hbc => dvd_trans hab hbc⟩

-- 2) 偏序三性质的直接陈述（最稳妥）
example : (∀ a : ℕ, a ∣ a) ∧ (∀ a b : ℕ, a ∣ b → b ∣ a → a = b) ∧
    (∀ a b c : ℕ, a ∣ b → b ∣ c → a ∣ c) :=
  ⟨fun a => dvd_refl a, fun a b => Nat.dvd_antisymm, fun a b c => dvd_trans⟩

-- 3) 全序的直接写法
example : ¬ (∀ a b : ℕ, a ∣ b ∨ b ∣ a) := by
  intro h
  rcases h 4 6 with h46 | h64
  · norm_num at h46
  · norm_num at h64

-- 4) 集合包含反方向：用 hfac 的 a^2 - b^2 形式
example (a b : ℤ) (h : a ^ 2 = b ^ 2) : b = a ∨ b = -a := by
  have hfac : a ^ 2 - b ^ 2 = (a - b) * (a + b) := by ring
  rw [← sub_eq_zero, hfac, mul_eq_zero, sub_eq_zero, add_eq_zero_iff_eq_neg] at h
  rcases h with h | h
  · exact Or.inl h.symm
  · exact Or.inr (by linarith)

end Dbg02b
