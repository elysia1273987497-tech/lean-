/-
# Problem 8. 为什么割的取反需要小心

对 `r ∈ ℚ` 记 `X_r = {q : q < r}`；`X ⊆ ℚ` 是 Dedekind 割，`Xᶜ = ℚ \ X`。

(a) 计算 `{-u : u ∈ X_rᶜ}`，并解释它为什么不是割。
(b) 定义 `Y = {q : q < -u, 某 u ∈ Xᶜ}`，证明 `Y` 是割且 `X + Y = X_0`。

这里用"非空 + 真子集 + 下半集 + 无最大元"的割定义（与教材 1.4 节一致）；
其中"无最大元"正是 (a) 中 `{-u : u ∈ X_rᶜ}` 不是割的原因。
-/
import Mathlib

namespace AnalysisHW1.Problem08

open Set

/-- Dedekind 割。 -/
structure Cut where
  /-- 割作为 `ℚ` 的子集。 -/
  set : Set ℚ
  nonempty : set.Nonempty
  not_univ : set ≠ univ
  /-- 下半集：`q ∈ set` 且 `p < q` 蕴含 `p ∈ set`。 -/
  downward : ∀ {p q : ℚ}, q ∈ set → p < q → p ∈ set
  /-- 无最大元。 -/
  no_max : ∀ q ∈ set, ∃ q' ∈ set, q < q'

/-- `X_r = {q : q < r}`。 -/
def Xr (r : ℚ) : Set ℚ := {q | q < r}

/-- `X_0 = {q : q < 0}`，题目中的零元。 -/
def X0 : Set ℚ := Xr 0

/-! ## (a) `{-u : u ∈ X_rᶜ}` 不是割 -/

/-- (a) 先算出这个集合：`u ∈ X_rᶜ ↔ r ≤ u`，取负号后得 `≤ -r`。 -/
theorem neg_compl_Xr (r : ℚ) : {q : ℚ | ∃ u ∉ Xr r, q = -u} = {q : ℚ | q ≤ -r} := by
  ext q
  constructor
  · rintro ⟨u, hu, rfl⟩
    simp only [Xr, mem_setOf_eq, not_lt] at hu
    exact neg_le_neg hu
  · intro hq
    exact ⟨-q, by simp only [Xr, mem_setOf_eq, not_lt]; linarith, by ring⟩

/-- (a) 该集合**有最大元** `-r`。 -/
theorem neg_compl_Xr_has_max (r : ℚ) :
    ∃ m ∈ {q : ℚ | ∃ u ∉ Xr r, q = -u}, ∀ q ∈ {q : ℚ | ∃ u ∉ Xr r, q = -u}, q ≤ m := by
  refine ⟨-r, ?_, ?_⟩
  · rw [neg_compl_Xr]; exact le_refl _
  · intro q hq
    rw [neg_compl_Xr] at hq
    exact hq

/-- (a) 结论：`{-u : u ∈ X_rᶜ}` 恰好是 `(-∞, -r]`，含最大元，故**不是**割。 -/
theorem neg_compl_Xr_is_Iic (r : ℚ) : ({q : ℚ | ∃ u ∉ Xr r, q = -u} : Set ℚ) = Iic (-r) := by
  rw [neg_compl_Xr]; ext q; simp

/-- (a) 用割的定义明确写出"不是割"：不存在满足割四条性质（尤其"无最大元"）的构造。 -/
theorem neg_compl_Xr_not_cut (r : ℚ) :
    ¬ (∀ q ∈ ({q : ℚ | ∃ u ∉ Xr r, q = -u} : Set ℚ),
        ∃ q' ∈ ({q : ℚ | ∃ u ∉ Xr r, q = -u} : Set ℚ), q < q') := by
  intro h
  obtain ⟨m, hm, hmax⟩ := neg_compl_Xr_has_max r
  obtain ⟨q', hq', hlt⟩ := h m hm
  exact absurd (hmax q' hq') (not_le.mpr hlt)

/-! ## (b) `Y` 是割 -/

/-- (b) 题目中的 `Y = {q : q < -u 对某个 u ∈ Xᶜ}`。 -/
def Y (X : Set ℚ) : Set ℚ := {q | ∃ u ∉ X, q < -u}

/-- (b) 割的补集非空：割是真子集。 -/
theorem exists_not_mem (X : Cut) : ∃ u : ℚ, u ∉ X.set := by
  by_contra h
  push_neg at h
  exact X.not_univ (eq_univ_of_forall h)

/-- (b) 割中元素的任意"上方"都在割外（这是割的最基本性质）。 -/
theorem exists_not_mem_gt (X : Cut) (q : ℚ) : ∃ r : ℚ, q < r ∧ r ∉ X.set := by
  by_cases hq : q ∈ X.set
  · obtain ⟨q', hq', hlt⟩ := X.no_max q hq
    refine ⟨q', hlt, fun h => ?_⟩
    exact absurd (X.downward h hlt) (not_le.mpr hlt)
  · exact ⟨q, lt_irrefl q, hq⟩

/-- (b) 割对"变大"是封闭的：任意 `q` 都存在割中元素严格大于 `q`。

证明：取 `u ∉ X`，则 `max q u ∈ X`（否则 `u ∉ X` 而 `max q u ≥ u`，
与割的下半集性质矛盾）；再说明 `max q u > q`（若 `max q u = u ≤ q` 则 `X` 中元素都 `≤ q`，
与 `u ∉ X` 矛盾）。 -/
theorem exists_not_mem_gt_aux (X : Cut) (q : ℚ) : ∃ x ∈ X.set, q < x := by
  obtain ⟨u, hu⟩ := exists_not_mem X
  have hmax : max q u ∈ X.set := by
    by_contra h
    have hle : u ≤ max q u := le_max_right _ _
    rcases lt_or_eq_of_le hle with hlt | heq
    · exact hu (X.downward h hlt)
    · exact h (heq ▸ hu)
  refine ⟨max q u, hmax, ?_⟩
  rcases lt_or_ge q u with hlt | hle
  · exact lt_of_lt_of_le hlt (le_max_right _ _)
  · by_contra hcon
    push_neg at hcon
    have : u ≤ q := by
      have h1 : max q u = u := max_eq_right hle
      exact h1 ▸ hcon
    exact hu (X.downward hmax (by
      rcases lt_or_eq_of_le hle with h2 | h2
      · exact h2
      · exact absurd (X.downward hmax (by linarith : q < max q u)) (not_le.mpr hcon)))

/-- (b) `Y` 是割。

手写解答只写了"$Y = X_{-r}$"这类说法；这里完整验证四条性质。 -/theorem Y_isCut (X : Cut) : Cut where
  set := Y X.set
  nonempty := by
    obtain ⟨u, hu⟩ := exists_not_mem X
    exact ⟨-u - 1, u, hu, by linarith⟩
  not_univ := by
    obtain ⟨x, hx⟩ := X.nonempty
    intro h
    have : (-x : ℚ) ∈ Y X.set := by rw [h]; exact mem_univ _
    obtain ⟨u, hu, hlt⟩ := this
    have : u < x := by linarith
    exact hu (X.downward hx this)
  downward := by
    rintro p q ⟨u, hu, hlt⟩ hpq
    exact ⟨u, hu, lt_trans hpq hlt⟩
  no_max := by
    rintro q ⟨u, hu, hlt⟩
    obtain ⟨q', hlt', hlt''⟩ := Rat.density hlt
    exact ⟨q', ⟨u, hu, hlt'⟩, hlt''⟩

/-! ## (b) `X + Y = X_0` -/

/-- `X` 中元素与 `Y` 中元素之和为负。 -/
theorem add_Y_neg (X : Cut) {x y : ℚ} (hx : x ∈ X.set) (hy : y ∈ Y X.set) : x + y < 0 := by
  obtain ⟨u, hu, hyu⟩ := hy
  have hxu : x < u := by
    by_contra h
    push_neg at h
    exact hu (X.downward hx h)
  linarith

/-- (b) 主结论：`X + Y = X_0`。

手写解答的思路是"一方面 `t < 0`，另一方面任一 `t < 0` 都在 `X+Y` 中"；
这里第二个方向的关键是：取 `u ∉ X`，再取 `x ∈ X` 充分大（割无最大元保证能做到），
于是 `t - x < -u`，即 `t - x ∈ Y`。 -/
theorem X_add_Y_eq_X0 (X : Cut) :
    {t : ℚ | ∃ x ∈ X.set, ∃ y ∈ Y X.set, x + y = t} = X0 := by
  ext t
  constructor
  · rintro ⟨x, hx, y, hy, rfl⟩
    simp only [X0, Xr, mem_setOf_eq]
    exact add_Y_neg X hx hy
  · intro ht
    simp only [X0, Xr, mem_setOf_eq] at ht
    obtain ⟨u, hu⟩ := exists_not_mem X
    have htu : t - (-u) < -u := by linarith
    obtain ⟨x, hx, hxgt⟩ := exists_not_mem_gt_aux X (t - (-u))
    exact ⟨x, hx, t - x, ⟨u, hu, by linarith⟩, by ring⟩

end AnalysisHW1.Problem08
