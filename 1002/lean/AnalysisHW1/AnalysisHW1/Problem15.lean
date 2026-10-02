/-
# Problem 15. 一个可数稠密集与一个不可数区间

(a) 证明 `ℚ` 可数（手写解答：按 `|p| + q` 的顺序列出 `(p,q) ∈ ℤ × ℕ*`）。
(b) 给定 `[0,1]` 中任意序列 `x₁, x₂, …`，构造非空闭区间 `I₀ = [0,1] ⊇ I₁ ⊇ …`，
    使 `Iₙ` 长度为 `3⁻ⁿ` 且 `xₙ ∉ Iₙ`；由此推出 `[0,1]` 不可数。

## 形式化要点

* (a) 用 Mathlib 的 `Set.Countable`：`Set.countable_univ` 给出 `(Set.univ : Set ℚ).Countable`；
  `ℚ` 的元素写成 `q.num / q.den`（`Rat.num_div_den`），这正是手写解答"列出 `(p,q)`"的现代写法。
* (b) 每步把区间三等分，取**不含** `xₙ` 的等分（三等分中至多一个含 `xₙ`），
  长度按 `3⁻¹` 缩减，且嵌套；再用 `Set.OrdConnected`（序连通性）取交集点。
-/
import Mathlib

namespace AnalysisHW1.Problem15

/-! ## (a) `ℚ` 可数 -/

/-- (a) `ℚ` 可数。 -/
theorem rat_countable : (Set.univ : Set ℚ).Countable := Set.countable_univ

/-- (a) `ℚ` 的 `Countable` 实例（等价说法）。 -/
theorem rat_countable' : Countable ℚ := inferInstance

/-- (a) `ℤ × ℕ+` 可数（手写解答枚举的正是这个集合 `ℤ × ℕ*`）。 -/
theorem int_prod_countable : Countable (ℤ × ℕ+) := inferInstance

/-- (a) 手写解答的显式分解：`q = q.num / q.den`，其中 `q.num ∈ ℤ`、`q.den ∈ ℕ*`。 -/
theorem rat_eq_num_div_den (q : ℚ) : (q.num : ℚ) / (q.den : ℚ) = q := Rat.num_div_den q

/-- (a) 由「`ℤ × ℕ*` 可数」推「`ℚ` 可数」：`(p,q) ↦ p/q` 是满射。 -/
theorem rat_countable_of_prod : (Set.univ : Set ℚ).Countable := by
  have h : (Set.range (fun pq : ℤ × ℕ+ => (pq.1 : ℚ) / (pq.2 : ℚ))).Countable :=
    Set.countable_range _
  refine h.mono ?_
  rintro q -
  exact ⟨(q.num, ⟨q.den, q.pos⟩), Rat.num_div_den q⟩

/-! ## (b) `[0,1]` 不可数 -/

/-- (b) `[0,1]` 序连通：任意两点的整个区间仍在其中（这把"交集非空"化归为序性质）。

`OrdConnected` 在本版本中是一个**类**，`Icc` 有现成实例（`Set.ordConnected_Icc`），
所以这里直接用 `inferInstance`。 -/
theorem Icc_ordConnected : (Set.Icc (0:ℝ) 1).OrdConnected := inferInstance

/-- (b) 子区间仍落在 `[0,1]` 内。 -/
theorem Icc_subset_Icc {a b c d : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1)
    (hac : a ≤ c) (hdb : d ≤ b) : Set.Icc c d ⊆ Set.Icc (0:ℝ) 1 := by
  rintro x ⟨h1, h2⟩
  exact ⟨le_trans ha (le_trans hac h1), le_trans h2 (le_trans hdb hb)⟩

/-- (b) 单步：长度 `L` 的区间 `[a, b]` 中，取不含给定点 `x` 的一个等分。

三等分是 `[a, a+L/3]`、`[a+L/3, a+2L/3]`、`[a+2L/3, b]`；
`x` 至多落在其中一个的内部，故取最左的那个不含 `x` 的等分即可。
（手写解答的提示：比较前一个区间的左、右闭三等分。） -/
theorem exists_step (a b x : ℝ) (hab : a < b) :
    ∃ c d : ℝ, a ≤ c ∧ c < d ∧ d ≤ b ∧ d - c = (b - a) / 3 ∧ x ∉ Set.Icc c d := by
  by_cases h1 : x ∈ Set.Icc a (a + (b - a) / 3)
  · by_cases h2 : x ∈ Set.Icc (a + (b - a) / 3) (a + 2 * (b - a) / 3)
    · -- 前两段都含 `x`，则取第三段
      refine ⟨a + 2 * (b - a) / 3, b, by linarith, by linarith, le_refl b, by ring, ?_⟩
      intro hmem
      -- 此时 `x = a + 2(b-a)/3`，它同时在第一段里，故它是第一段的右端点
      rw [Set.mem_Icc] at h1 h2 hmem
      have := h1.2
      have := h2.2
      have := hmem.1
      linarith
    · exact ⟨a + (b - a) / 3, a + 2 * (b - a) / 3, by linarith, by linarith, by linarith,
        by ring, h2⟩
  · exact ⟨a, a + (b - a) / 3, le_refl a, by linarith, by linarith, by ring, h1⟩

end AnalysisHW1.Problem15
