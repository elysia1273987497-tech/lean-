/-
# Problem 2. 一个偏序及其极值元

`D = {1,2,3,4,6,12}`，按整除排序 `a ⪯ b ↔ a ∣ b`。

(a) 验证是偏序，但不是全序。
(b) 对 `A = {4,6}`：求所有上界/下界、极大/极小元、`sup_D A` 与 `inf_D A`，
    并判断 `A` 是否有最大/最小元。

注：`IsPartialOrder` / `IsTotal` 在本版本 Mathlib 中是**类**而非可直接匿名构造的结构，
所以这里把偏序三条性质与"非全序"直接写成命题。手写解答 (b) 未给出 `sup_D A`、`inf_D A`。
-/
import Mathlib

namespace AnalysisHW1.Problem02

/-- 题目中的集合 `D = {1,2,3,4,6,12}`。 -/
def D : Finset ℕ := {1, 2, 3, 4, 6, 12}

/-- 题目中的子集 `A = {4,6}`。 -/
def A : Finset ℕ := {4, 6}

/-! ## (a) 偏序，且非全序 -/

/-- (a) 整除在 `ℕ` 上满足偏序三性质。 -/
theorem dvd_partialOrder :
    (∀ a : ℕ, a ∣ a) ∧
    (∀ a b : ℕ, a ∣ b → b ∣ a → a = b) ∧
    (∀ a b c : ℕ, a ∣ b → b ∣ c → a ∣ c) :=
  ⟨fun a => dvd_refl a, fun _ _ => Nat.dvd_antisymm, fun _ _ _ => dvd_trans⟩

/-- (a) 整除**不是**全序：`4` 与 `6` 互不整除。 -/
theorem dvd_not_total : ¬ (∀ a b : ℕ, a ∣ b ∨ b ∣ a) := by
  intro h
  rcases h 4 6 with h46 | h64
  · norm_num at h46
  · norm_num at h64

/-! ## (b) `A = {4,6}` 在 `D` 中的界与极值元 -/

/-- `A` 在 `D` 中的上界（`Finset`）。 -/
def upperBoundsA : Finset ℕ := D.filter fun d => ∀ a ∈ A, a ∣ d

/-- `A` 在 `D` 中的下界（`Finset`）。 -/
def lowerBoundsA : Finset ℕ := D.filter fun d => ∀ a ∈ A, d ∣ a

/-- (b) `D` 中 `A` 的上界恰为 `{12}`。 -/
theorem upperBoundsA_eq : upperBoundsA = {12} := by decide

/-- (b) `D` 中 `A` 的下界恰为 `{1, 2}`。 -/
theorem lowerBoundsA_eq : lowerBoundsA = {1, 2} := by decide

/-- (b) `A` 中无最大元。 -/
theorem no_max_in_A : ¬ ∃ m ∈ A, ∀ a ∈ A, a ∣ m := by decide

/-- (b) `A` 中无最小元。 -/
theorem no_min_in_A : ¬ ∃ m ∈ A, ∀ a ∈ A, m ∣ a := by decide

/-- (b) `4` 是 `A` 的极大元。 -/
theorem four_maximal : 4 ∈ A ∧ ∀ a ∈ A, 4 ∣ a → a = 4 := by decide

/-- (b) `4` 是 `A` 的极小元。 -/
theorem four_minimal : 4 ∈ A ∧ ∀ a ∈ A, a ∣ 4 → a = 4 := by decide

/-- (b) `6` 是 `A` 的极大元。 -/
theorem six_maximal : 6 ∈ A ∧ ∀ a ∈ A, 6 ∣ a → a = 6 := by decide

/-- (b) `6` 是 `A` 的极小元。 -/
theorem six_minimal : 6 ∈ A ∧ ∀ a ∈ A, a ∣ 6 → a = 6 := by decide

/-- (b) `sup_D A = 12`：`12` 是 `D` 中 `A` 的最小上界。 -/
theorem sup_D_A : 12 ∈ D ∧ (∀ a ∈ A, a ∣ 12) ∧ ∀ d ∈ D, (∀ a ∈ A, a ∣ d) → 12 ∣ d := by
  decide

/-- (b) `inf_D A = 2`：`2` 是 `D` 中 `A` 的最大下界。 -/
theorem inf_D_A : 2 ∈ D ∧ (∀ a ∈ A, 2 ∣ a) ∧ ∀ d ∈ D, (∀ a ∈ A, d ∣ a) → d ∣ 2 := by
  decide

/-- (b) `A` 的极大元集合恰为 `{4,6}`。 -/
theorem maximal_set : A.filter (fun m => ∀ a ∈ A, m ∣ a → a = m) = {4, 6} := by decide

/-- (b) `A` 的极小元集合恰为 `{4,6}`。 -/
theorem minimal_set : A.filter (fun m => ∀ a ∈ A, a ∣ m → a = m) = {4, 6} := by decide

end AnalysisHW1.Problem02
