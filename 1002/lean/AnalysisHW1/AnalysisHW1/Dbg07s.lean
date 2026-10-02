import Mathlib

namespace Dbg07s

-- 用 Int.le_floor 证 ⌊b⌋ ≤ a + 1
example {a b : ℝ} (h : 1 < b - a) : (⌊b⌋ : ℝ) ≤ a + 1 := by
  have h1 : b < a + 2 := by linarith
  have h2 : ⌊b⌋ ≤ ⌊a + 2⌋ := Int.floor_mono (le_of_lt h1)
  have h3 : ⌊a + 2⌋ = ⌊a⌋ + 2 := by
    rw [Int.floor_add_intCast]
  have h4 : (⌊a⌋ : ℝ) ≤ a := Int.floor_le a
  have h5 : (⌊b⌋ : ℝ) ≤ (⌊a⌋ : ℝ) + 2 := by
    rw [h3] at h2
    push_cast at h2
    exact_mod_cast h2
  linarith

end Dbg07s
