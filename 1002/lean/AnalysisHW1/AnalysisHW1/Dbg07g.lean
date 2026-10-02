import Mathlib

namespace Dbg07g

-- 复现 exists_int_div_between 的核心
example {a b : ℝ} {n : ℕ} (hn : 0 < n) (h : 1 < (n : ℝ) * (b - a)) :
    ∃ m : ℤ, a < (m : ℝ) / n ∧ (m : ℝ) / n < b := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h' : (n : ℝ) * a + 1 < (n : ℝ) * b := by linarith
  have hfl : (n : ℝ) * b < (⌊(n : ℝ) * b⌋ : ℝ) + 1 := Int.lt_floor_add_one _
  have hcle : (n : ℝ) * a < (⌊(n : ℝ) * b⌋ : ℝ) := by linarith
  have hle2 : (⌊(n : ℝ) * b⌋ : ℝ) ≤ (n : ℝ) * b := Int.floor_le _
  refine ⟨⌊(n : ℝ) * b⌋, ?_, ?_⟩
  · rw [lt_div_iff₀ hn']
    exact hcle
  · rw [div_lt_iff₀ hn']
    exact lt_of_le_of_lt hle2 (Int.lt_floor_add_one _)

-- 复现 hnpos
example {t : ℝ} (ht : 0 < t) : True := by
  obtain ⟨n, hn⟩ := exists_nat_gt t
  have hnpos : 0 < n := by
    by_contra h
    push_neg at h
    have h0 : n = 0 := Nat.le_zero.mp h
    subst h0
    norm_num at hn
  trivial

-- 复现 hf_gt_a
example {a b : ℝ} (hab : a < b) (f : ℕ → ℝ)
    (hf1 : ∀ n, b - (b - a) / ((n : ℝ) + 1) < f n) : ∀ n, a < f n := by
  intro n
  have h1 := hf1 n
  have hb : (0 : ℝ) < b - a := by linarith
  have hfrac : (b - a) / ((n : ℝ) + 1) < b - a := by
    have hlt : (1 : ℝ) < (n : ℝ) + 1 := by
      have : (0 : ℝ) ≤ n := by positivity
      linarith
    rw [div_lt_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 1)]
    nlinarith
  linarith

end Dbg07g
