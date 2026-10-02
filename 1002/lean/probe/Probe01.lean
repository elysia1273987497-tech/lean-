import Mathlib.Order.Basic
import Mathlib.Data.Real.Basic

namespace ApiProbe

example {a b : ℝ} (h : 1 < b - a) : ∃ m : ℤ, a < (m : ℝ) ∧ (m : ℝ) < b := by
  set S : Set ℤ := {k | a < (k : ℝ)} with hS
  have hSne : S.Nonempty := by
    obtain ⟨k, hk⟩ := exists_int_gt a
    exact ⟨k, hk⟩
  obtain ⟨m, hmS, hmin⟩ := Int.exists_least_of_bddBelow ⟨a, fun k hk => le_of_lt hk⟩ hSne
  have ham : a < (m : ℝ) := hmS
  refine ⟨m, ham, ?_⟩
  by_contra hcon
  push_neg at hcon
  have hnot : (m - 1 : ℤ) ∉ S := by
    intro hmem
    have : ((m - 1 : ℤ) : ℝ) < (m : ℝ) := by push_cast; linarith
    exact absurd (hmin (m - 1) hmem) (not_le.mpr this)
  simp only [hS, Set.mem_setOf_eq, not_lt] at hnot
  push_cast at hnot
  linarith

example : ∃ k : ℕ, (1 : ℝ) < 2 ^ k := by
  obtain ⟨k, hk⟩ := Nat.exists_pow_gt (R := ℝ) (by norm_num : (0:ℝ) < 1)
  exact ⟨k, by simpa using hk⟩

example : Irrational (Real.sqrt 2) := irrational_sqrt_two

end ApiProbe
