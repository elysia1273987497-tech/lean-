/-
# Problem 12. 实数算术的刚性

设 `f : ℝ → ℝ` 满足

  `f(x + y) = f(x) + f(y)`,  `f(xy) = f(x)·f(y)`   (`x, y ∈ ℝ`).

证明：要么 `f ≡ 0`，要么 `f = id`。
不得假设 `f` 保持 `1`、单射、保序或连续。（可用 Problem 11。）

## 证明结构

1. 由 `f(x) = f(x)·f(1)` 得 `f(1) = f(1)²`，即 `f(1) ∈ {0, 1}`。
2. 若 `f(1) = 0` 则 `f ≡ 0`。
3. 若 `f(1) ≠ 0`，则 `f(1) = 1`；此时 `f` 是环自同态，故 `f(q) = q`（`q ∈ ℚ`）。
4. `x ≥ 0` 时 `x = (√x)²`（**用到 Problem 11**：正数有平方根），故 `f(x) = f(√x)² ≥ 0`，
   即 `f` 保序。
5. 结合 `f|_ℚ = id` 与保序性，由 `ℚ` 在 `ℝ` 中稠密得 `f = id`。
-/
import Mathlib

namespace AnalysisHW1.Problem12

variable {f : ℝ → ℝ}

/-- 加法性。 -/
def Additive' (f : ℝ → ℝ) : Prop := ∀ x y, f (x + y) = f x + f y

/-- 乘法性。 -/
def Multiplicative' (f : ℝ → ℝ) : Prop := ∀ x y, f (x * y) = f x * f y

/-- (0) `f(0) = 0`。 -/
theorem f_zero (ha : Additive' f) : f 0 = 0 := by
  have h : f 0 = f 0 + f 0 := by simpa using ha 0 0
  linarith

/-- (1) `f(1) ∈ {0, 1}`。 -/
theorem f_one_eq_zero_or_one (hm : Multiplicative' f) : f 1 = 0 ∨ f 1 = 1 := by
  have h : f 1 = f 1 * f 1 := by simpa using hm 1 1
  have h2 : f 1 * (f 1 - 1) = 0 := by linarith
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact Or.inl h3
  · exact Or.inr (by linarith)

/-- (2) 若 `f 1 = 0` 则 `f ≡ 0`。 -/
theorem eq_zero_of_f_one_eq_zero (hm : Multiplicative' f) (h1 : f 1 = 0) :
    ∀ x, f x = 0 := by
  intro x
  have h : f x = f x * f 1 := by simpa using hm x 1
  rw [h, h1, mul_zero]

/-- (3) `f 1 = 1` 时 `f` 是环自同态。 -/
noncomputable def toRingHom (ha : Additive' f) (hm : Multiplicative' f) (h1 : f 1 = 1) :
    ℝ →+* ℝ where
  toFun := f
  map_one' := h1
  map_mul' := hm
  map_zero' := f_zero ha
  map_add' := ha

/-- (3) 于是 `f` 在 `ℚ` 上是恒等。 -/
theorem rat_eq (ha : Additive' f) (hm : Multiplicative' f) (h1 : f 1 = 1) (q : ℚ) :
    f (q : ℝ) = (q : ℝ) := by
  have h := map_ratCast (toRingHom ha hm h1) q
  rw [show (toRingHom ha hm h1) q = f (q : ℝ) from rfl] at h
  exact h

/-- (4) `f` 保序（非严格）：`0 ≤ x` 时 `0 ≤ f x`。

用 Problem 11 的结论：正数有平方根（`Real.sq_sqrt`），故 `f x = f (√x)² ≥ 0`。 -/
theorem nonneg_of_nonneg (ha : Additive' f) (hm : Multiplicative' f) (h1 : f 1 = 1)
    {x : ℝ} (hx : 0 ≤ x) : 0 ≤ f x := by
  have hsq : Real.sqrt x * Real.sqrt x = x := by rw [← sq, Real.sq_sqrt hx]
  have hmul : f (Real.sqrt x * Real.sqrt x) =
      f (Real.sqrt x) * f (Real.sqrt x) := hm _ _
  have h : f x = f (Real.sqrt x) * f (Real.sqrt x) :=
    calc f x = f (Real.sqrt x * Real.sqrt x) := by rw [hsq]
      _ = f (Real.sqrt x) * f (Real.sqrt x) := hm _ _
  rw [h]
  exact mul_self_nonneg _

/-- (5) 主结论：要么 `f ≡ 0`，要么 `f = id`。 -/
theorem rigid (ha : Additive' f) (hm : Multiplicative' f) :
    (∀ x, f x = 0) ∨ (∀ x, f x = x) := by
  rcases f_one_eq_zero_or_one hm with h1 | h1
  · exact Or.inl (eq_zero_of_f_one_eq_zero hm h1)
  · refine Or.inr ?_
    have hneg : ∀ x : ℝ, f (-x) = -f x := by
      intro x
      have h2 : f (x + (-x)) = f x + f (-x) := ha x (-x)
      rw [add_neg_cancel, f_zero ha] at h2
      linarith
    have hmono : ∀ x y : ℝ, x ≤ y → f x ≤ f y := by
      intro x y hxy
      have h := nonneg_of_nonneg ha hm h1 (sub_nonneg.mpr hxy)
      have hadd : f (y - x) = f y - f x := by
        have h3 : f (y + (-x)) = f y + f (-x) := ha y (-x)
        rw [← sub_eq_add_neg] at h3
        rw [h3, hneg x, sub_eq_add_neg]
      linarith [hadd ▸ h]
    intro x
    rcases lt_trichotomy (f x) x with hlt | heq | hgt
    · -- `f x < x`：取有理数 `q` 使 `f x < q < x`，与 `f` 在 `ℚ` 上恒等 + 保序矛盾
      obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hlt
      have hqid := rat_eq ha hm h1 q
      have hle := hmono (q : ℝ) x hq2.le
      rw [hqid] at hle
      linarith
    · exact heq
    · -- `x < f x`：对称处理
      obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hgt
      have hqid := rat_eq ha hm h1 q
      have hle := hmono x (q : ℝ) hq1.le
      rw [hqid] at hle
      linarith

end AnalysisHW1.Problem12
