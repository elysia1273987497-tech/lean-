import Mathlib

namespace Probe11b

#check @pow_le_one₀
#check @pow_le_one
#check @pow_le_pow_right₀
#check @pow_le_pow_right
#check @one_le_pow
#check @pow_le_pow_left₀
#check @pow_le_pow_left

-- 0 < a < 1 且 n ≥ 1 时 a^n ≤ a
example {a : ℝ} (h0 : 0 < a) (h1 : a < 1) {n : ℕ} (hn : 1 ≤ n) : a ^ n ≤ a := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [pow_add, pow_one]
  have : a ^ m ≤ 1 := pow_le_one₀ h0.le h1.le
  nlinarith

end Probe11b
