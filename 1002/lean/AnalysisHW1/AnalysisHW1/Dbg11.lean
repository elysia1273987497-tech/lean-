import Mathlib

namespace Dbg11

-- 1) E_bddAbove 的核心
example {a t : ℝ} (hn : 1 ≤ (2:ℕ)) (htn : t ^ 2 ≤ a) : t ≤ max a 1 := by
  by_contra hc
  push_neg at hc
  have ht1 : 1 ≤ t := le_trans (le_max_right a 1) hc.le
  have hle : t ≤ t ^ 2 := by
    have h1 : t ^ 1 ≤ t ^ 2 := pow_le_pow_right₀ ht1 hn
    simpa using h1
  have hta : a < t := lt_of_le_of_lt (le_max_left a 1) hc
  linarith

-- 2) x ≤ R 的 csSup_le
example {E : Set ℝ} {x R : ℝ} (hx : x = sSup E)
    (hub : ∀ t ∈ E, t ≤ R) (hne : E.Nonempty) : x ≤ R := by
  rw [hx]
  exact csSup_le hne hub

-- 3) 取 t 逼近 x
example {E : Set ℝ} {x φ : ℝ} (hφ : 0 < φ) (hne : E.Nonempty) (hx : x = sSup E)
    (hbdd : BddAbove E) : ∃ t ∈ E, x - φ < t := by
  have hlt : x - φ < x := by linarith
  rw [hx] at hlt ⊢
  exact exists_lt_of_lt_csSup hne hlt

end Dbg11
