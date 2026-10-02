/-
# Problem 4. 上确界、下确界与取到性

(a) 求 `A = {n/(n+1) : n ∈ ℕ*}` 与 `B = {q ∈ ℚ : -2 < q ≤ 3}` 在 `ℝ` 中的 sup/inf，判断是否取到。
(b) 确定 `∅` 的所有实上界/下界，并说明 `sup_ℝ ∅`、`inf_ℝ ∅` 不作为实数存在。

说明：`B` 是 `ℚ` 的子集，而 `ℚ` 不完备（`B` 在 `ℚ` 中无上确界），
所以 (a) 中 `B` 的部分按题意在 `ℝ` 中处理：`B` 在 `ℝ` 中的 sup 为 `3`、inf 为 `-2`，
且 `3` 被取到（`3 ∈ ℚ ∩ B`）、`-2` 不被取到。
-/
import Mathlib

namespace AnalysisHW1.Problem04

open Set

/-- 题目中的集合 `A = {n/(n+1) : n ∈ ℕ*}`。 -/
def Aset : Set ℝ := {x | ∃ n : ℕ, 0 < n ∧ x = n / (n + 1)}

/-- 题目中的集合 `B = {q ∈ ℚ : -2 < q ≤ 3}`（作为 `ℝ` 的子集）。 -/
def Bset : Set ℝ := {x | ∃ q : ℚ, -2 < q ∧ q ≤ 3 ∧ (q : ℝ) = x}

/-! ## (a) 集合 `A` -/

/-- `A` 非空。 -/
theorem Aset_nonempty : Aset.Nonempty := ⟨1 / 2, 1, by norm_num, by norm_num⟩

/-- `1` 是 `A` 的上界。 -/
theorem one_upperBound : ∀ a ∈ Aset, a ≤ 1 := by
  rintro x ⟨n, hn, rfl⟩
  have h : (0 : ℝ) < n + 1 := by positivity
  rw [div_le_one h]
  push_cast
  linarith

/-- `1/2` 是 `A` 的下界。 -/
theorem half_lowerBound : ∀ a ∈ Aset, 1 / 2 ≤ a := by
  rintro x ⟨n, hn, rfl⟩
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h : (0 : ℝ) < n + 1 := by positivity
  rw [le_div_iff₀ h]
  nlinarith

/-- 手写解答中的关键步骤：对任意 `α < 1`，存在 `n` 使 `α < n/(n+1)`。
手写解答取 `n > α/(1-α)`，这里用 Archimedes 性质直接取得这样的 `n`。 -/
theorem exists_lt_Aset {α : ℝ} (hα : α < 1) : ∃ a ∈ Aset, α < a := by
  obtain ⟨n, hn⟩ := exists_nat_gt (α / (1 - α))
  have hpos : 0 < 1 - α := by linarith
  refine ⟨n / (n + 1), ⟨n + 1, by positivity, by ring⟩, ?_⟩
  have hn' : (0 : ℝ) < n + 1 := by positivity
  rw [lt_div_iff₀ hn']
  have h1 : α * (1 - α) < n * (1 - α) := by
    rw [div_lt_iff₀ hpos] at hn
    linarith
  nlinarith

/-- (a) `sup A = 1`，且 `1` 不被取到。 -/
theorem Aset_sSup : sSup Aset = 1 := by
  apply le_antisymm
  · apply csSup_le Aset_nonempty one_upperBound
  · by_contra h
    push_neg at h
    obtain ⟨a, ha, hlt⟩ := exists_lt_Aset h
    exact absurd (le_csSup ⟨1, one_upperBound⟩ ha) (not_le.mpr hlt)

/-- (a) `inf A = 1/2`，且 `1/2` 不被取到。 -/
theorem Aset_sInf : sInf Aset = 1 / 2 := by
  apply le_antisymm
  · by_contra h
    push_neg at h
    have hmem : (1 / 2 : ℝ) ∈ lowerBounds Aset := by
      intro a ha
      by_contra hlt
      push_neg at hlt
      exact absurd (le_csInf ⟨1 / 2, half_lowerBound⟩ ⟨a, ha, hlt⟩) (not_le.mpr h)
    exact absurd (le_csInf ⟨1 / 2, half_lowerBound⟩ hmem) (not_le.mpr h)
  · exact csInf_le ⟨1 / 2, half_lowerBound⟩ (by norm_num [Aset, show (1 : ℝ) / 2 = 1 / (1 + 1) by norm_num])

/-- (a) `1 ∉ A`：上确界不被取到。 -/
theorem one_not_mem_Aset : (1 : ℝ) ∉ Aset := by
  rintro ⟨n, hn, h⟩
  have hn' : (0 : ℝ) < n + 1 := by positivity
  rw [div_eq_one_iff_eq (ne_of_gt hn')] at h
  push_cast at h
  linarith

/-- (a) `1/2 ∈ A`：下确界**被取到**（`n = 1`）。

注意：这与手写解答不同。手写解答写"下界为 `(-∞,1/2]`"暗示 `1/2` 是下界，
但 `1/2 ∈ A` 说明下确界确实被取到，手写解答没有明确指出这一点。 -/
theorem half_mem_Aset : (1 / 2 : ℝ) ∈ Aset := by
  refine ⟨1, by norm_num, ?_⟩
  norm_num

/-! ## (a) 集合 `B` -/

/-- `B` 非空。 -/
theorem Bset_nonempty : Bset.Nonempty := ⟨0, 0, by norm_num, by norm_num, by norm_num⟩

/-- `3` 是 `B` 在 `ℝ` 中的上界，且被取到。 -/
theorem three_upperBound : ∀ b ∈ Bset, b ≤ 3 := by
  rintro x ⟨q, -, hq, rfl⟩
  exact_mod_cast hq

theorem three_mem_Bset : (3 : ℝ) ∈ Bset := ⟨3, by norm_num, le_refl _, by norm_num⟩

/-- `-2` 是 `B` 在 `ℝ` 中的下界。 -/
theorem neg_two_lowerBound : ∀ b ∈ Bset, -2 ≤ b := by
  rintro x ⟨q, hq, -, rfl⟩
  exact_mod_cast le_of_lt hq

/-- (a) `sup B = 3`（在 `ℝ` 中）。 -/
theorem Bset_sSup : sSup Bset = 3 := by
  apply le_antisymm
  · apply csSup_le Bset_nonempty three_upperBound
  · exact le_csSup ⟨3, three_upperBound⟩ three_mem_Bset

/-- (a) `inf B = -2`（在 `ℝ` 中）。 -/
theorem Bset_sInf : sInf Bset = -2 := by
  apply le_antisymm
  · exact csInf_le ⟨-2, neg_two_lowerBound⟩ ⟨-(3 : ℚ), by norm_num, by norm_num, by norm_num⟩
  · apply le_csInf Bset_nonempty neg_two_lowerBound

/-- (a) `-2 ∉ B`：`B` 的下确界不被取到。 -/
theorem neg_two_not_mem_Bset : (-2 : ℝ) ∉ Bset := by
  rintro ⟨q, hq, -, hqx⟩
  have : (-2 : ℚ) < q := hq
  have : ((-2 : ℚ) : ℝ) < (q : ℝ) := by exact_mod_cast this
  rw [← hqx] at this
  exact lt_irrefl _ this

/-- (a) `B` 的下确界在 `ℝ` 中可取到性补充：`-2` 不是 `B` 的元素，
但 `B` 中确实有任意接近 `-2` 的元素（供参考）。 -/
theorem Bset_approach_inf : ∀ ε > 0, ∃ b ∈ Bset, b < -2 + ε := by
  intro ε hε
  obtain ⟨n, hn⟩ := exists_nat_gt (1 / ε)
  have hnpos : (0 : ℝ) < n := by positivity
  refine ⟨-2 + 1 / (n + 1), ?_, by linarith [div_pos one_pos (by positivity : (0:ℝ) < n + 1)]⟩
  refine ⟨(-2 : ℚ) + 1 / (n + 1), ?_, ?_, by push_cast; ring⟩
  · push_cast
    linarith [div_pos one_pos (by positivity : (0:ℚ) < n + 1)]
  · push_cast
    have : (1 : ℚ) / (n + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith
    linarith

/-! ## (b) 空集的上界与下界 -/

/-- (b) 每个实数都是 `∅` 的上界。 -/
theorem empty_upperBounds : upperBounds (∅ : Set ℝ) = univ := by
  ext x
  simp [upperBounds]

/-- (b) 每个实数都是 `∅` 的下界。 -/
theorem empty_lowerBounds : lowerBounds (∅ : Set ℝ) = univ := by
  ext x
  simp [lowerBounds]

/-- (b) 不存在 `s` 使 `s = sup_ℝ ∅`（即 `s` 是 `∅` 的最小上界）。

证明：`∅` 没有上界可以再"往下压"——对任意候选 `s`，`s - 1` 仍是上界且 `s - 1 < s`。 -/
theorem no_sSup_empty : ¬ ∃ s : ℝ, IsLUB (∅ : Set ℝ) s := by
  rintro ⟨s, hs, hleast⟩
  have hbdd : ∀ x : ℝ, x ∈ upperBounds (∅ : Set ℝ) := by
    intro x
    rw [empty_upperBounds]
    exact mem_univ x
  exact absurd (hleast (s - 1) (hbdd (s - 1))) (not_le.mpr (by linarith))

/-- (b) 不存在 `s` 使 `s = inf_ℝ ∅`。 -/
theorem no_sInf_empty : ¬ ∃ s : ℝ, IsGLB (∅ : Set ℝ) s := by
  rintro ⟨s, hs, hgreat⟩
  have hbdd : ∀ x : ℝ, x ∈ lowerBounds (∅ : Set ℝ) := by
    intro x
    rw [empty_lowerBounds]
    exact mem_univ x
  exact absurd (hgreat (s + 1) (hbdd (s + 1))) (not_le.mpr (by linarith))

/-- (b) 说明：`ℝ` 作为条件完备格把 `sSup ∅` 记作 `0`，这只是形式化约定，
并不是"空集的上确界"这个数学对象存在——上一条给出了不存在性的严格证明。 -/
theorem sSup_empty_convention : sSup (∅ : Set ℝ) = 0 := csSup_empty

end AnalysisHW1.Problem04
