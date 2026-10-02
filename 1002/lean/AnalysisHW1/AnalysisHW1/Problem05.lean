/-
# Problem 5. 整数部分

对 `x ∈ ℝ`，`⌊x⌋` 是唯一满足 `m ≤ x < m+1` 的整数 `m`。

(a) 证明 `⌊x⌋ + ⌊y⌋ ≤ ⌊x+y⌋ ≤ ⌊x⌋ + ⌊y⌋ + 1`，并举例说明两端的等号都能取到。
(b) 用 `⌊x⌋` 表示 `⌊-x⌋`，区分 `x ∈ ℤ` 与 `x ∉ ℤ`；特别地计算 `⌊-7/3⌋`。
-/
import Mathlib

namespace AnalysisHW1.Problem05

open Int

/-- 取整的基本刻画：`m ≤ r < m+1` 时 `⌊r⌋ = m`。 -/
theorem floor_eq_of_bounds {r : ℝ} {m : ℤ} (h1 : (m : ℝ) ≤ r) (h2 : r < (m : ℝ) + 1) :
    ⌊r⌋ = m :=
  Int.floor_eq_iff.mpr ⟨h1, h2⟩

/-! ## (a) 取整加法不等式 -/

/-- (a) 下界：`⌊x⌋ + ⌊y⌋ ≤ ⌊x + y⌋`。

由 `⌊x⌋ ≤ x`、`⌊y⌋ ≤ y` 相加得 `⌊x⌋+⌊y⌋ ≤ x+y`，
再用 `Int.le_floor`（`m ≤ ⌊r⌋ ↔ (m:ℝ) ≤ r`）把它翻译回整数不等式。 -/
theorem floor_add_floor_le (x y : ℝ) : ⌊x⌋ + ⌊y⌋ ≤ ⌊x + y⌋ := by
  apply Int.le_floor.mpr
  push_cast
  linarith [Int.floor_le x, Int.floor_le y]

/-- (a) 上界：`⌊x + y⌋ ≤ ⌊x⌋ + ⌊y⌋ + 1`。

手写解答说"`x₀+y₀ ≤ x+y < x₀+y₀+2`，故 `⌊x+y⌋` 只能是 `x₀+y₀` 或 `x₀+y₀+1`"；
形式化时用反证：若 `⌊x⌋+⌊y⌋+2 ≤ ⌊x+y⌋`，则 `x+y ≥ ⌊x⌋+⌊y⌋+2`，
与 `x < ⌊x⌋+1`、`y < ⌊y⌋+1` 矛盾。 -/
theorem floor_add_le (x y : ℝ) : ⌊x + y⌋ ≤ ⌊x⌋ + ⌊y⌋ + 1 := by
  have hx : x < (⌊x⌋ : ℝ) + 1 := Int.lt_floor_add_one x
  have hy : y < (⌊y⌋ : ℝ) + 1 := Int.lt_floor_add_one y
  by_contra h
  push_neg at h
  have h2 : ((⌊x⌋ + ⌊y⌋ + 2 : ℤ) : ℝ) ≤ x + y := by
    have h3 : (⌊x⌋ + ⌊y⌋ + 2 : ℤ) ≤ ⌊x + y⌋ := by omega
    have h4 : ((⌊x⌋ + ⌊y⌋ + 2 : ℤ) : ℝ) ≤ ((⌊x + y⌋ : ℤ) : ℝ) := by exact_mod_cast h3
    linarith [Int.floor_le (x + y)]
  push_cast at h2
  linarith

/-- (a) 两个不等式合起来的完整陈述。 -/
theorem floor_add_bounds (x y : ℝ) :
    ⌊x⌋ + ⌊y⌋ ≤ ⌊x + y⌋ ∧ ⌊x + y⌋ ≤ ⌊x⌋ + ⌊y⌋ + 1 :=
  ⟨floor_add_floor_le x y, floor_add_le x y⟩

/-- (a) 下界取等的例子：`x = y = 1/3`（`⌊1/3⌋ + ⌊1/3⌋ = 0 = ⌊2/3⌋`）。

**注意**：手写解答举的 `(x,y) = (1/2,1/2)` 其实取到的是**上**界
（`⌊1/2⌋+⌊1/2⌋ = 0` 而 `⌊1⌋ = 1`），并没有取到下界。 -/
theorem witness_lower : ⌊(1 / 3 : ℝ)⌋ + ⌊(1 / 3 : ℝ)⌋ = ⌊(1 / 3 : ℝ) + 1 / 3⌋ := by
  have h1 : ⌊(1 / 3 : ℝ)⌋ = 0 := floor_eq_of_bounds (by norm_num) (by norm_num)
  have h2 : ⌊(1 / 3 : ℝ) + 1 / 3⌋ = 0 := by
    apply floor_eq_of_bounds <;> norm_num
  rw [h1, h2]; norm_num

/-- (a) 上界取等的例子：`x = y = 1/2`（`⌊1⌋ = 1 = ⌊1/2⌋ + ⌊1/2⌋ + 1`）——
这正是手写解答举的例子。 -/
theorem witness_upper : ⌊(1 / 2 : ℝ) + 1 / 2⌋ = ⌊(1 / 2 : ℝ)⌋ + ⌊(1 / 2 : ℝ)⌋ + 1 := by
  norm_num

/-- (a) 另一个上界取等的例子：`x = y = 3/4`。 -/
theorem witness_upper' : ⌊(3 / 4 : ℝ) + 3 / 4⌋ = ⌊(3 / 4 : ℝ)⌋ + ⌊(3 / 4 : ℝ)⌋ + 1 := by
  norm_num

/-- (a) 说明手写解答举的 `(ε,0)` 其实取下界（只要 `0 ≤ ε < 1`）。 -/
theorem witness_eps_zero (ε : ℝ) (h0 : 0 ≤ ε) (h1 : ε < 1) :
    ⌊ε⌋ + ⌊(0 : ℝ)⌋ = ⌊ε + 0⌋ := by
  rw [add_zero]
  have : ⌊ε⌋ = 0 := Int.floor_eq_zero_iff.mpr ⟨h0, h1⟩
  rw [this]
  norm_num

/-! ## (b) `⌊-x⌋` 与 `⌊x⌋` -/

/-- (b) 若 `x` 是整数，则 `⌊-x⌋ = -⌊x⌋`。 -/
theorem floor_neg_of_int (m : ℤ) : ⌊-(m : ℝ)⌋ = -⌊(m : ℝ)⌋ := by
  have h1 : ⌊(m : ℝ)⌋ = m := Int.floor_intCast m
  have h2 : ⌊-(m : ℝ)⌋ = -m := by
    apply floor_eq_of_bounds <;> push_cast <;> linarith
  rw [h1, h2]

/-- (b) 若 `x` 不是整数，则 `⌊-x⌋ = -⌊x⌋ - 1`。

手写解答：设 `⌊x⌋ < x < ⌊x⌋+1`（严格，因为 `x ∉ ℤ`），
则 `-⌊x⌋-1 < -x < -⌊x⌋`，故 `⌊-x⌋ = -⌊x⌋-1`，
即 `-⌊x⌋-1 ≤ -x < -⌊x⌋`。 -/
theorem floor_neg_of_not_int (x : ℝ) (hx : ∀ m : ℤ, (m : ℝ) ≠ x) :
    ⌊-x⌋ = -⌊x⌋ - 1 := by
  have hlt : x < (⌊x⌋ : ℝ) + 1 := Int.lt_floor_add_one x
  have hne : x ≠ (⌊x⌋ : ℝ) := fun h => hx ⌊x⌋ h.symm
  have hgt : (⌊x⌋ : ℝ) < x := lt_of_le_of_ne (Int.floor_le x) (Ne.symm hne)
  apply floor_eq_of_bounds
  · push_cast; linarith
  · push_cast; linarith

/-- (b) 统一表述：`x ∈ ℤ` 时 `⌊-x⌋ = -⌊x⌋`，否则 `⌊-x⌋ = -⌊x⌋-1`。 -/
theorem floor_neg_cases (x : ℝ) :
    (x ∈ Set.range ((↑) : ℤ → ℝ) → ⌊-x⌋ = -⌊x⌋) ∧
    (x ∉ Set.range ((↑) : ℤ → ℝ) → ⌊-x⌋ = -⌊x⌋ - 1) := by
  constructor
  · rintro ⟨m, rfl⟩
    exact floor_neg_of_int m
  · intro hx
    exact floor_neg_of_not_int x (by rintro m rfl; exact hx ⟨m, rfl⟩)

/-- (b) `7/3` 不是整数（这条用整数算术直接证明，避免取整推理的绕路）。 -/
theorem seven_thirds_not_int : ∀ m : ℤ, (m : ℝ) ≠ 7 / 3 := by
  intro m hm
  have h : (3 : ℝ) * (m : ℝ) = 7 := by
    rw [hm]; norm_num
  have h3 : (3 * m : ℤ) = 7 := by exact_mod_cast h
  omega

/-- (b) 特别地：`⌊-7/3⌋ = -3`。 -/
theorem floor_neg_seven_thirds : ⌊-(7 / 3 : ℝ)⌋ = -3 := by
  have h1 : ⌊(7 / 3 : ℝ)⌋ = 2 := by
    apply floor_eq_of_bounds <;> norm_num
  have h2 : ⌊-(7 / 3 : ℝ)⌋ = -⌊(7 / 3 : ℝ)⌋ - 1 :=
    floor_neg_of_not_int _ seven_thirds_not_int
  rw [h2, h1]
  norm_num

/-- (b) 与 `floor_neg_of_not_int` 交叉验证。 -/
theorem floor_neg_seven_thirds' : ⌊-(7 / 3 : ℝ)⌋ = -⌊(7 / 3 : ℝ)⌋ - 1 :=
  floor_neg_of_not_int _ seven_thirds_not_int

end AnalysisHW1.Problem05
