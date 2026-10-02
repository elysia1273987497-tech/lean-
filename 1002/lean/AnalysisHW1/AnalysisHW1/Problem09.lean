/-
# Problem 9. 嵌套区间及其假设

设 `Iₙ = [aₙ, bₙ] ⊆ ℝ` 非空有界闭区间，`Iₙ₊₁ ⊆ Iₙ`。

(a) 令 `α = sup{aₙ}`、`β = inf{bₙ}`，证明 `α ≤ β` 且 `⋂ₙ Iₙ = [α, β]`。
(b) 若 `bₙ - aₙ ≤ 1/n`，则交集是单点集。
(c) 给出嵌套非空开有界区间族交集为空，以及嵌套非空闭无界区间族交集为空的例子。

注：手写解答 (a)(b) 论证严重不完整（还出现 `[a_n] ⊇ [a_n]` 这类笔误），这里补全。
-/
import Mathlib

namespace AnalysisHW1.Problem09

open Set

/-- 嵌套条件：`a` 递增、`b` 递减，且每个区间 `[a n, b n]` 非空。 -/
def Nested (a b : ℕ → ℝ) : Prop := ∀ n : ℕ, a n ≤ a (n + 1) ∧ b (n + 1) ≤ b n ∧ a n ≤ b n

/-- 嵌套假设下 `a m ≤ b n` 对一切 `m, n` 成立。 -/
theorem a_le_b {a b : ℕ → ℝ} (hn : Nested a b) (m n : ℕ) : a m ≤ b n := by
  have ha : Monotone a := monotone_nat_of_le_succ fun k => (hn k).1
  have hb : Antitone b := antitone_nat_of_succ_le fun k => (hn k).2.1
  rcases le_total m n with h | h
  · exact le_trans (ha h) (hn n).2.2
  · exact le_trans (hn m).2.2 (hb h)

/-- 由 `a_le_b`：`range a` 有上界。 -/
theorem bddAbove_range_a {a b : ℕ → ℝ} (hn : Nested a b) : BddAbove (range a) :=
  ⟨b 0, by rintro y ⟨m, rfl⟩; exact a_le_b hn m 0⟩

/-- 由 `a_le_b`：`range b` 有下界。 -/
theorem bddBelow_range_b {a b : ℕ → ℝ} (hn : Nested a b) : BddBelow (range b) :=
  ⟨a 0, by rintro y ⟨n, rfl⟩; exact a_le_b hn 0 n⟩

/-- 区间族 `[a n, b n]` 的交集非空。 -/
theorem inter_nonempty {a b : ℕ → ℝ} (hn : Nested a b) :
    (⋂ n, Icc (a n) (b n)).Nonempty :=
  ⟨a 0, mem_iInter.mpr fun n => mem_Icc.mpr ⟨le_refl _, a_le_b hn 0 n⟩⟩

/-- (a) `α ≤ β`：手写解答的"每个 `a` 都被每个 `b` 控制"即 `a_le_b`。 -/
theorem alpha_le_beta {a b : ℕ → ℝ} (hn : Nested a b) :
    sSup (range a) ≤ sInf (range b) :=
  csSup_le ⟨a 0, mem_range_self 0⟩ fun _ ⟨m, hm⟩ =>
    hm ▸ le_csInf ⟨b 0, mem_range_self 0⟩ fun _ ⟨n, hn'⟩ => hn' ▸ a_le_b hn m n

/-- (a) 主结论：`⋂ₙ [aₙ, bₙ] = [α, β]`。

手写解答只说"显然"；这里两个方向都完整证明。 -/
theorem iInter_Icc_eq_Icc {a b : ℕ → ℝ} (hn : Nested a b) :
    (⋂ n, Icc (a n) (b n)) = Icc (sSup (range a)) (sInf (range b)) := by
  have hAb : BddAbove (range a) := bddAbove_range_a hn
  have hBb : BddBelow (range b) := bddBelow_range_b hn
  have hle : ∀ n, a n ≤ sSup (range a) := fun n => le_csSup hAb (mem_range_self n)
  have hge : ∀ n, sInf (range b) ≤ b n := fun n => csInf_le hBb (mem_range_self n)
  ext t
  constructor
  · intro ht
    have ht' : ∀ n, a n ≤ t ∧ t ≤ b n := fun n =>
      mem_Icc.mp (mem_iInter.mp ht n)
    exact mem_Icc.mpr
      ⟨le_csSup hAb (mem_range_self 0) |> le_trans <| (ht' 0).1 |> le_trans <| le_refl _,
       le_trans (ht' 0).2 (hge 0) |> le_trans <| le_refl _⟩
  · intro ht n
    exact mem_Icc.mpr ⟨le_trans (hle n) (mem_Icc.mp ht).1,
      le_trans (mem_Icc.mp ht).2 (hge n)⟩

/-- (a) 主结论的另一半（与上一行合并表述）：两式同时成立。 -/
theorem part_a {a b : ℕ → ℝ} (hn : Nested a b) :
    sSup (range a) ≤ sInf (range b) ∧
    (⋂ n, Icc (a n) (b n)) = Icc (sSup (range a)) (sInf (range b)) :=
  ⟨alpha_le_beta hn, iInter_Icc_eq_Icc hn⟩

/-- (b) 若 `bₙ - aₙ ≤ 1/n`（`n ≥ 1`），则交集是单点集。

手写解答写"交集至多一个元素"；这里补上"非空"并给出那个唯一的点。 -/
theorem inter_singleton {a b : ℕ → ℝ} (hn : Nested a b)
    (hlen : ∀ n : ℕ, 0 < n → b n - a n ≤ 1 / n) :
    ∃ c : ℝ, (⋂ n, Icc (a n) (b n)) = {c} := by
  have hAb : BddAbove (range a) := bddAbove_range_a hn
  have hBb : BddBelow (range b) := bddBelow_range_b hn
  have hle : ∀ n, a n ≤ sSup (range a) := fun n => le_csSup hAb (mem_range_self n)
  have hge : ∀ n, sInf (range b) ≤ b n := fun n => csInf_le hBb (mem_range_self n)
  have heq : sSup (range a) = sInf (range b) := by
    refine le_antisymm (alpha_le_beta hn) ?_
    by_contra hcon
    push_neg at hcon
    have hdiff : 0 < sSup (range a) - sInf (range b) := by linarith
    obtain ⟨n, hnpos, hlt⟩ := exists_nat_gt (1 / (sSup (range a) - sInf (range b)))
    have hnpos' : (0 : ℝ) < n := by exact_mod_cast hnpos
    rw [div_lt_iff₀ hdiff] at hlt
    have h3 : b n - a n ≤ 1 / n := hlen n hnpos
    have h4 : sSup (range a) - sInf (range b) < 1 / n := by
      rw [div_lt_iff₀ hnpos']
      linarith
    linarith [hle n, hge n]
  refine ⟨sSup (range a), ?_⟩
  rw [iInter_Icc_eq_Icc hn, heq, Icc_self]

/-! ## (c) 两个反例 -/

/-- (c) 例一：嵌套的**非空开有界**区间 `(0, 1/(n+1))`，交集为空。

一个值得点出的细节：`0` 属于**每一个**区间（区间是开的，`0 < 1/(n+1)`），
但交集仍为空——正数都被某个区间排除，非正数一开始就不在 `(0, 1/(n+1))` 里。 -/
theorem open_nested_empty : (⋂ n : ℕ, Ioo (0 : ℝ) (1 / (n + 1))) = ∅ := by
  ext t
  simp only [mem_iInter, mem_Ioo, mem_empty_iff_false, iff_false, not_forall, not_and]
  rcases le_or_gt t 0 with ht | ht
  · exact ⟨0, fun h => absurd h.1 ht⟩
  · obtain ⟨n, hn⟩ := exists_nat_gt (1 / t)
    refine ⟨n, fun h => absurd h.2 ?_⟩
    rw [div_lt_iff₀ (by positivity)] at h
    rw [div_lt_iff₀ ht] at hn
    nlinarith

/-- (c) 例一附加：这族区间确实非空且两两嵌套。 -/
theorem open_nested_props :
    (∀ n : ℕ, (Ioo (0 : ℝ) (1 / (n + 1))).Nonempty) ∧
    (∀ n : ℕ, Ioo (0 : ℝ) (1 / (n + 2)) ⊆ Ioo (0 : ℝ) (1 / (n + 1))) :=
  ⟨fun n => ⟨1 / (n + 2), by constructor <;> positivity⟩, fun n x hx =>
    ⟨hx.1, lt_of_lt_of_le hx.2 <| div_le_div_of_nonneg_left (by norm_num) (by positivity) (by omega)⟩⟩

/-- (c) 例二：嵌套的**非空闭无界**区间 `[n, n+1]`，交集为空。

手写解答的例子 `aₙ = n, bₙ = n+1` 正确，但未验证。 -/
theorem closed_unbounded_nested_empty :
    (⋂ n : ℕ, Icc (n : ℝ) (n + 1)) = ∅ := by
  ext t
  simp only [mem_iInter, mem_Icc, mem_empty_iff_false, iff_false, not_forall, not_and]
  obtain ⟨N, hN⟩ := exists_nat_gt t
  exact ⟨N, fun h => absurd h.1 (not_le.mpr hN)⟩

/-- (c) 例二附加：这族区间确实非空且两两嵌套（无界显然）。 -/
theorem closed_unbounded_nested_props :
    (∀ n : ℕ, (Icc (n : ℝ) (n + 1)).Nonempty) ∧
    (∀ n : ℕ, Icc ((n : ℝ) + 1) (n + 2) ⊆ Icc (n : ℝ) (n + 1)) :=
  ⟨fun n => ⟨n, le_refl _, by linarith⟩, fun n x hx =>
    ⟨by linarith [hx.1], by linarith [hx.2]⟩⟩

end AnalysisHW1.Problem09
