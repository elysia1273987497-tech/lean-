/-
# Problem 6. 上确界与下确界的算术

设 `A, B ⊆ ℝ` 非空有界。

(a) 证明 `s = sup A` 当且仅当 `s` 是 `A` 的上界，且对每个 `ε > 0` 存在 `a ∈ A` 使 `s - ε < a`。
(b) 定义 `A + B = {a+b}`, `A - B = {a-b}`，证明
    `sup (A+B) = sup A + sup B`, `inf (A-B) = inf A - sup B`。

## 本版本 Mathlib 的适配要点

* `Set ℝ` **没有** `+` / `-` 实例（`A + B` 不合法），所以 Minkowski 和/差写成显式 `def`，
  非空性与有界性也手写证明。
* 不等式 `a ≤ b` 的常用判据是 `le_of_forall_pos_lt_add`：
  `(∀ ε > 0, a < b + ε) → a ≤ b`。（比 `sInf` 的 `ε` 刻画好用，后者容易把
  `s` 与 `sInf A` 混淆。）

## 证明策略（与手写解答一致）

* (a) 两个方向：`⟸` 用 `csSup_le`；`⟹` 用反证 + `csSup_le`。
* (b) `sup(A+B)`：`sup A + sup B` 是上界（`add_le_add`），
  且对任意 `ε` 取 `a, b` 分别逼近 `sup A`、`sup B`（各用 `ε/2`），得 `(sup A + sup B) - ε < a+b`。
* (b) `inf(A-B)`：下界方向 `sub_le_sub (csInf_le _) (le_csSup _)`；
  上界方向用 `le_of_forall_pos_lt_add`，取 `a` 逼近 `inf A`（`a < inf A + ε/2`）、
  `b` 逼近 `sup B`（`sup B - ε/2 < b`），得 `inf A - sup B < (a-b) + ε`。
-/
import Mathlib

namespace AnalysisHW1.Problem06

open Set

/-- Minkowski 和：`A + B = {a + b : a ∈ A, b ∈ B}`。 -/
def addSet (A B : Set ℝ) : Set ℝ := {x | ∃ a ∈ A, ∃ b ∈ B, a + b = x}

/-- Minkowski 差：`A - B = {a - b : a ∈ A, b ∈ B}`。 -/
def subSet (A B : Set ℝ) : Set ℝ := {x | ∃ a ∈ A, ∃ b ∈ B, a - b = x}

variable {A B : Set ℝ}

/-! ## (a) 上确界的 `ε` 刻画 -/

/-- (a) `⟸`：`s` 是上界且下方任意接近 ⟹ `s = sup A`。 -/
theorem sSup_of_upperBound_and_approx (hne : A.Nonempty) (hub : ∀ a ∈ A, a ≤ s)
    (happrox : ∀ ε > 0, ∃ a ∈ A, s - ε < a) : sSup A = s := by
  refine le_antisymm (csSup_le hne hub) ?_
  by_contra h
  push_neg at h
  obtain ⟨a, ha, hlt⟩ := happrox (s - sSup A) (by linarith)
  have hle : a ≤ sSup A := le_csSup ⟨s, hub⟩ ha
  linarith

/-- (a) `⟹`：`s = sup A` ⟹ `s` 是上界且下方任意接近。 -/
theorem approx_of_sSup (hne : A.Nonempty) (hbdd : BddAbove A) (hs : sSup A = s) :
    (∀ a ∈ A, a ≤ s) ∧ (∀ ε > 0, ∃ a ∈ A, s - ε < a) := by
  subst hs
  refine ⟨fun a ha => le_csSup hbdd ha, ?_⟩
  intro ε hε
  by_contra h
  push_neg at h
  have : sSup A ≤ sSup A - ε := csSup_le hne fun a ha => by linarith [h a ha]
  linarith

/-- (a) 完整陈述（`⟺`）。 -/
theorem sSup_iff (hne : A.Nonempty) (hbdd : BddAbove A) :
    sSup A = s ↔ (∀ a ∈ A, a ≤ s) ∧ (∀ ε > 0, ∃ a ∈ A, s - ε < a) :=
  ⟨approx_of_sSup hne hbdd, fun h => sSup_of_upperBound_and_approx hne h.1 h.2⟩

/-- 下确界的对偶刻画：`s = inf A` ⟹ `s` 是下界且上方任意接近。 -/
theorem approx_of_sInf (hne : A.Nonempty) (hbdd : BddBelow A) (hs : sInf A = s) :
    (∀ a ∈ A, s ≤ a) ∧ (∀ ε > 0, ∃ a ∈ A, a < s + ε) := by
  subst hs
  refine ⟨fun a ha => csInf_le hbdd ha, ?_⟩
  intro ε hε
  by_contra h
  push_neg at h
  have : sInf A + ε ≤ sInf A := le_csInf hne fun a ha => by linarith [h a ha]
  linarith

/-! ## (b) `sup (A+B) = sup A + sup B` -/

theorem addSet_nonempty (hA : A.Nonempty) (hB : B.Nonempty) : (addSet A B).Nonempty := by
  obtain ⟨a, ha⟩ := hA
  obtain ⟨b, hb⟩ := hB
  exact ⟨a + b, a, ha, b, hb, rfl⟩

theorem addSet_bddAbove (hA : BddAbove A) (hB : BddAbove B) : BddAbove (addSet A B) := by
  obtain ⟨M, hM⟩ := hA
  obtain ⟨N, hN⟩ := hB
  exact ⟨M + N, by rintro x ⟨a, ha, b, hb, rfl⟩; exact add_le_add (hM ha) (hN hb)⟩

/-- (b) `sup (A+B) = sup A + sup B`。 -/
theorem sSup_addSet (hA : A.Nonempty) (hB : B.Nonempty)
    (hAb : BddAbove A) (hBb : BddAbove B) : sSup (addSet A B) = sSup A + sSup B := by
  refine sSup_of_upperBound_and_approx (addSet_nonempty hA hB) ?_ ?_
  · rintro x ⟨a, ha, b, hb, rfl⟩
    exact add_le_add (le_csSup hAb ha) (le_csSup hBb hb)
  · intro ε hε
    obtain ⟨a, ha, ha'⟩ := (approx_of_sSup hA hAb rfl).2 (ε / 2) (by linarith)
    obtain ⟨b, hb, hb'⟩ := (approx_of_sSup hB hBb rfl).2 (ε / 2) (by linarith)
    exact ⟨a + b, ⟨a, ha, b, hb, rfl⟩, by linarith⟩

/-! ## (b) `inf (A-B) = inf A - sup B` -/

theorem subSet_nonempty (hA : A.Nonempty) (hB : B.Nonempty) : (subSet A B).Nonempty := by
  obtain ⟨a, ha⟩ := hA
  obtain ⟨b, hb⟩ := hB
  exact ⟨a - b, a, ha, b, hb, rfl⟩

theorem subSet_bddBelow (hA : BddBelow A) (hB : BddAbove B) : BddBelow (subSet A B) := by
  obtain ⟨M, hM⟩ := hA
  obtain ⟨N, hN⟩ := hB
  exact ⟨M - N, by rintro x ⟨a, ha, b, hb, rfl⟩; exact sub_le_sub (hM ha) (hN hb)⟩

/-- (b) `inf (A-B) = inf A - sup B`。 -/
theorem sInf_subSet (hA : A.Nonempty) (hB : B.Nonempty)
    (hAb : BddBelow A) (hBb : BddAbove B) : sInf (subSet A B) = sInf A - sSup B := by
  have hbdd : BddBelow (subSet A B) := subSet_bddBelow hAb hBb
  have hne : (subSet A B).Nonempty := subSet_nonempty hA hB
  -- 两个方向其实是同一个不等式链：
  -- `sInf A - sSup B` 是 `A - B` 的下界，故 `≤ sInf (A-B)`（用 `le_csInf`）；
  -- 反向由 `sInf (A-B) ≤ a - b` 与 `le_csInf` 反用给出。
  -- 下面先建立关键不等式，再用 `le_antisymm`。
  have hlb : sInf A - sSup B ≤ sInf (subSet A B) :=
    le_csInf hne fun x hx => by
      obtain ⟨a, ha, b, hb, rfl⟩ := hx
      exact sub_le_sub (csInf_le hAb ha) (le_csSup hBb hb)
  have hub : sInf (subSet A B) ≤ sInf A - sSup B := by
    by_contra h
    push_neg at h
    -- 记 `δ = sInf (A-B) - (sInf A - sSup B) > 0`。
    -- 取 `a` 逼近 `sInf A`（`a < sInf A + δ/4`）、`b` 逼近 `sSup B`（`sSup B - δ/4 < b`），
    -- 则 `a - b < sInf A - sSup B + δ/2 < sInf (A-B)`，与 `sInf (A-B) ≤ a - b` 矛盾。
    set δ : ℝ := sInf (subSet A B) - (sInf A - sSup B) with hδ
    have hδpos : 0 < δ := by rw [hδ]; linarith
    obtain ⟨a, ha, ha'⟩ := (approx_of_sInf hA hAb rfl).2 (δ / 4) (by linarith)
    obtain ⟨b, hb, hb'⟩ := (approx_of_sSup hB hBb rfl).2 (δ / 4) (by linarith)
    have hmem : sInf (subSet A B) ≤ a - b := csInf_le hbdd ⟨a, ha, b, hb, rfl⟩
    rw [hδ] at ha' hb'
    linarith
  exact le_antisymm hub hlb

end AnalysisHW1.Problem06
