/-
# Problem 11. 由完备性构造正根

固定 `a > 0` 与整数 `n ≥ 2`。

(a) 证明 `E = {t ∈ ℝ : t ≥ 0, tⁿ ≤ a}` 非空、有上界，且 `x = sup E` 为正。
(b) 证明 `xⁿ = a`，且没有其他正实数的 `n` 次幂等于 `a`。

**证明要点**（与手写解答一致，但把"极限/连续性"换成题目提示的有限恒等式）：

* 有限恒等式 `uᵏ - vᵏ = (u - v)·Σ_{j<k} u^{k-1-j}v^j`（`pow_sub_pow_factor`）
  给出扰动估计 `|u^{k+1} - v^{k+1}| ≤ (k+1)·Rᵏ·|u - v|`（`abs_pow_sub_pow_le`）。
* `xⁿ ≤ a`：对任意 `t ∈ E` 有 `tⁿ ≤ a`；取 `t` 任意接近 `x`，用扰动估计得 `xⁿ ≤ a + ε`。
* `xⁿ ≥ a`：若 `xⁿ < a`，取小 `φ > 0` 使 `(x+φ)ⁿ < a`，则 `x + φ ∈ E` 且 `φ > 0`，
  与 `x` 是 `E` 的上界矛盾。
-/
import Mathlib

namespace AnalysisHW1.Problem11

/-- (a) 集合 `E = {t : 0 ≤ t ∧ t^n ≤ a}`。 -/
def E (a : ℝ) (n : ℕ) : Set ℝ := {t | 0 ≤ t ∧ t ^ n ≤ a}

variable {a : ℝ} {n : ℕ}

/-! ## 有限恒等式与扰动估计 -/

/-- 题目提示的有限恒等式：`u^{k+1} - v^{k+1} = (u - v)·Σ_{j ≤ k} u^{k-j} v^j`。

证明用望远镜求和：`Σ_{j≤k}(P(j+1) - P(j)) = P(k+1) - P(0)`，其中 `P(j) = u^{k+1-j}v^j`。 -/
theorem pow_sub_pow_factor (u v : ℝ) (k : ℕ) :
    u ^ (k + 1) - v ^ (k + 1) =
      (u - v) * ∑ j ∈ Finset.range (k + 1), u ^ (k - j) * v ^ j := by
  rw [Finset.mul_sum]
  have hterm : ∀ j ∈ Finset.range (k + 1),
      (u - v) * (u ^ (k - j) * v ^ j) =
        u ^ (k + 1 - j) * v ^ j - u ^ (k - j) * v ^ (j + 1) := by
    intro j hj
    have hjk : j ≤ k := by
      have := Finset.mem_range.mp hj
      omega
    have h1 : k + 1 - j = (k - j) + 1 := by omega
    rw [h1, pow_succ]
    ring
  rw [Finset.sum_congr rfl hterm]
  have htel : ∀ m : ℕ, m ≤ k + 1 →
      ∑ j ∈ Finset.range m,
        (u ^ (k + 1 - j) * v ^ j - u ^ (k - j) * v ^ (j + 1)) =
        u ^ (k + 1) * v ^ 0 - u ^ (k + 1 - m) * v ^ m := by
    intro m hm
    induction m with
    | zero => simp
    | succ m ih =>
      have hm' : m ≤ k + 1 := by omega
      rw [Finset.sum_range_succ, ih hm']
      have h1 : k + 1 - m = (k + 1 - (m + 1)) + 1 := by omega
      have h2 : k - m = k + 1 - (m + 1) := by omega
      rw [h1, h2, pow_succ]
      ring
  rw [htel (k + 1) le_rfl]
  have hzero : k + 1 - (k + 1) = 0 := by omega
  rw [hzero]
  ring

/-- 辅助：`|Σ_{j ≤ k} u^{k-j} v^j| ≤ (k+1)·R^k`（当 `0 ≤ u, v ≤ R`）。 -/
theorem abs_sum_le (u v R : ℝ) (k : ℕ) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (huR : u ≤ R) (hvR : v ≤ R) :
    |∑ j ∈ Finset.range (k + 1), u ^ (k - j) * v ^ j| ≤ ((k + 1 : ℕ) : ℝ) * R ^ k := by
  have hR : 0 ≤ R := le_trans hu huR
  calc |∑ j ∈ Finset.range (k + 1), u ^ (k - j) * v ^ j|
      ≤ ∑ j ∈ Finset.range (k + 1), |u ^ (k - j) * v ^ j| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j ∈ Finset.range (k + 1), u ^ (k - j) * v ^ j := by
        apply Finset.sum_congr rfl
        intro j _
        rw [abs_of_nonneg (mul_nonneg (pow_nonneg hu _) (pow_nonneg hv _))]
    _ ≤ ∑ _j ∈ Finset.range (k + 1), R ^ k := by
        apply Finset.sum_le_sum
        intro j hj
        have hjle : j ≤ k := by
          have := Finset.mem_range.mp hj
          omega
        have h1 : u ^ (k - j) ≤ R ^ (k - j) := pow_le_pow_left₀ hu huR _
        have h2 : v ^ j ≤ R ^ j := pow_le_pow_left₀ hv hvR _
        calc u ^ (k - j) * v ^ j ≤ R ^ (k - j) * R ^ j :=
              mul_le_mul h1 h2 (pow_nonneg hv _) (pow_nonneg hR _)
          _ = R ^ k := by
              rw [← pow_add]
              congr 1
              omega
    _ = ((k + 1 : ℕ) : ℝ) * R ^ k := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- 扰动估计：`|u^{k+1} - v^{k+1}| ≤ (k+1)·R^k·|u - v|`（当 `0 ≤ u, v ≤ R`）。 -/
theorem abs_pow_sub_pow_le (u v R : ℝ) (k : ℕ) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (huR : u ≤ R) (hvR : v ≤ R) :
    |u ^ (k + 1) - v ^ (k + 1)| ≤ ((k + 1 : ℕ) : ℝ) * R ^ k * |u - v| := by
  rw [pow_sub_pow_factor, abs_mul]
  have h := abs_sum_le u v R k hu hv huR hvR
  calc |u - v| * |∑ j ∈ Finset.range (k + 1), u ^ (k - j) * v ^ j|
      ≤ |u - v| * (((k + 1 : ℕ) : ℝ) * R ^ k) :=
        mul_le_mul_of_nonneg_left h (abs_nonneg _)
    _ = ((k + 1 : ℕ) : ℝ) * R ^ k * |u - v| := by ring

/-! ## (a) `E` 的性质 -/

/-- `E` 非空（`0 ∈ E`，因 `a > 0`）。 -/
theorem E_nonempty (ha : 0 < a) (hn : 0 < n) : (E a n).Nonempty :=
  ⟨0, le_refl _, by rw [zero_pow hn.ne']; exact ha.le⟩

/-- `E` 的元素都被 `max a 1` 控制。 -/
theorem E_le_max (ha : 0 < a) (hn : 1 ≤ n) {t : ℝ} (ht : t ∈ E a n) : t ≤ max a 1 := by
  by_contra hc
  push_neg at hc
  have ht1 : 1 ≤ t := le_trans (le_max_right a 1) hc.le
  have hle : t ≤ t ^ n := by
    have h1 : t ^ 1 ≤ t ^ n := pow_le_pow_right₀ ht1 hn
    simpa using h1
  have hta : a < t := lt_of_le_of_lt (le_max_left a 1) hc
  linarith [ht.2]

/-- `E` 有上界：`max a 1` 是上界。 -/
theorem E_bddAbove (ha : 0 < a) (hn : 1 ≤ n) : BddAbove (E a n) :=
  ⟨max a 1, fun _ ht => E_le_max ha hn ht⟩

/-- (a) `x = sup E` 为正。 -/
theorem sup_pos (ha : 0 < a) (hn : 0 < n) : 0 < sSup (E a n) := by
  have hn1 : 1 ≤ n := hn
  rcases le_or_gt 1 a with ha1 | ha1
  · have hmem : (1 : ℝ) ∈ E a n := ⟨zero_le_one, by simpa using ha1⟩
    exact lt_of_lt_of_le one_pos (le_csSup (E_bddAbove ha hn1) hmem)
  · have hmem : a ∈ E a n := by
      refine ⟨ha.le, ?_⟩
      have h1 : a ^ n ≤ a ^ 1 := pow_le_pow_of_le_one ha.le ha1.le hn1
      simpa using h1
    exact lt_of_lt_of_le ha (le_csSup (E_bddAbove ha hn1) hmem)

/-! ## (b) `x^n = a` 与唯一性 -/

/-- `R ≥ 1`、`n ≥ 1` 时 `1 ≤ n·R^{n-1}`。 -/
theorem one_le_coef {R : ℝ} (hR : 1 ≤ R) {n : ℕ} (hn : 1 ≤ n) :
    1 ≤ (n : ℝ) * R ^ (n - 1) := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hpow : (1 : ℝ) ≤ R ^ (n - 1) := one_le_pow₀ hR
  nlinarith

/-- (b) 主结论：`(sup E)^n = a`。 -/
theorem sup_pow_eq (ha : 0 < a) (hn2 : 2 ≤ n) : (sSup (E a n)) ^ n = a := by
  have hn1 : 1 ≤ n := le_trans (by norm_num) hn2
  have hn0 : 0 < n := lt_of_lt_of_le (by norm_num) hn2
  have h0mem : (0 : ℝ) ∈ E a n := ⟨le_refl 0, by rw [zero_pow hn0.ne']; exact ha.le⟩
  set x := sSup (E a n) with hxdef
  set R := max a 1 with hRdef
  have hxR : x ≤ R := hxdef ▸ csSup_le ⟨0, h0mem⟩ (fun t ht => E_le_max ha hn1 ht)
  have hR1 : 1 ≤ R := hRdef ▸ le_max_right a 1
  have hRpos : 0 < R := lt_of_lt_of_le ha (hRdef ▸ le_max_left a 1)
  have hxpos : 0 < x := hxdef ▸ sup_pos ha hn0
  have hbddE : BddAbove (E a n) := E_bddAbove ha hn1
  have hmem_le : ∀ t ∈ E a n, t ≤ x := fun t ht => hxdef ▸ le_csSup hbddE ht
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt_case | hgt_case
  · -- `x^n < a`：构造 `t ∈ E` 与 `φ > 0` 使 `x < t + φ` 且 `(t+φ)^n < a`
    have hgap : 0 < a - x ^ n := by linarith
    set C : ℝ := (n : ℝ) * (R + 1) ^ (n - 1) + 1 with hCdef
    have hCpos : 0 < C := by rw [hCdef]; positivity
    set φ : ℝ := min (min (x / 2) 1) ((a - x ^ n) / C) with hφdef
    have hφ0 : 0 < φ := by
      rw [hφdef]
      exact lt_min (lt_min (by linarith) one_pos) (div_pos hgap hCpos)
    have hφx : φ ≤ x / 2 := by
      rw [hφdef]; exact (min_le_left _ _).trans (min_le_left _ _)
    have hφgap : C * φ < a - x ^ n := by
      have hbound2 : φ ≤ (a - x ^ n) / C := by
        rw [hφdef]; exact min_le_right _ _
      calc C * φ ≤ C * ((a - x ^ n) / C) :=
            mul_le_mul_of_nonneg_left hbound2 hCpos.le
        _ = a - x ^ n := mul_div_cancel₀ _ (ne_of_gt hCpos)
    -- 取 `t ∈ E` 且 `x - φ < t`
    obtain ⟨t, htE, htx⟩ := exists_lt_of_lt_csSup ⟨0, h0mem⟩ (by linarith : x - φ < x)
    have ht0 : 0 ≤ t := htE.1
    have htx_le : t ≤ x := hmem_le t htE
    have htR : t ≤ R := le_trans htx_le hxR
    have hxt : x < t + φ := by linarith
    have htφ_R : t + φ ≤ R + 1 := by linarith
    have hbound := abs_pow_sub_pow_le (t + φ) t (R + 1) (n - 1) (by linarith) ht0
      htφ_R (by linarith)
    have habs : |(t + φ) - t| = φ := by
      rw [add_sub_cancel_left]; exact abs_of_pos hφ0
    rw [habs] at hbound
    have hle : (t + φ) ^ (n - 1 + 1) - t ^ (n - 1 + 1) ≤
        ((n - 1 + 1 : ℕ) : ℝ) * (R + 1) ^ (n - 1) * φ := le_of_abs_le hbound
    have hn_eq : n - 1 + 1 = n := Nat.sub_add_cancel hn1
    rw [hn_eq] at hle
    have hcoef_le : ((n : ℕ) : ℝ) * (R + 1) ^ (n - 1) * φ ≤ C * φ := by
      rw [hCdef]
      have h2 : (0 : ℝ) < (R + 1) ^ (n - 1) := by positivity
      nlinarith [pow_pos hRpos (n - 1)]
    have hfinal : (t + φ) ^ n < a := by linarith
    have hmem : t + φ ∈ E a n := ⟨by linarith, le_of_lt hfinal⟩
    have hle2 := le_csSup (E_bddAbove ha hn1) hmem
    linarith
  · -- `a < x^n`：构造更小的上界
    have hgap : 0 < x ^ n - a := by linarith
    set ψ : ℝ := min (x / 2) ((x ^ n - a) / ((n : ℝ) * R ^ (n - 1))) with hψdef
    have hcoef_pos : 0 < (n : ℝ) * R ^ (n - 1) := by positivity
    have hψ0 : 0 < ψ := by
      rw [hψdef]
      exact lt_min (by linarith) (div_pos hgap hcoef_pos)
    have hψx : ψ ≤ x / 2 := by
      rw [hψdef]; exact min_le_left _ _
    have hψgap : ((n : ℝ) * R ^ (n - 1)) * ψ < x ^ n - a := by
      have hle : ψ ≤ (x ^ n - a) / ((n : ℝ) * R ^ (n - 1)) := by
        rw [hψdef]; exact min_le_right _ _
      calc ((n : ℝ) * R ^ (n - 1)) * ψ
          ≤ ((n : ℝ) * R ^ (n - 1)) * ((x ^ n - a) / ((n : ℝ) * R ^ (n - 1))) :=
            mul_le_mul_of_nonneg_left hle hcoef_pos.le
        _ = x ^ n - a := mul_div_cancel₀ _ (ne_of_gt hcoef_pos)
    have hsub_pos : 0 < x - ψ := by linarith
    have hsub_R : x - ψ ≤ R := by linarith
    have hbound := abs_pow_sub_pow_le x (x - ψ) R (n - 1) hxpos.le hsub_pos.le hxR hsub_R
    have habs : |x - (x - ψ)| = ψ := by
      rw [sub_sub_cancel]; exact abs_of_pos hψ0
    rw [habs] at hbound
    have hle : x ^ (n - 1 + 1) - (x - ψ) ^ (n - 1 + 1) ≤
        ((n - 1 + 1 : ℕ) : ℝ) * R ^ (n - 1) * ψ := le_of_abs_le hbound
    have hn_eq : n - 1 + 1 = n := Nat.sub_add_cancel hn1
    rw [hn_eq] at hle
    have hfinal : a < (x - ψ) ^ n := by linarith
    -- `x - ψ` 也是 `E` 的上界，且严格小于 `x`，与最小性矛盾
    have hub : ∀ t ∈ E a n, t ≤ x - ψ := by
      intro t ht
      by_contra hc
      push_neg at hc
      have htn : a < t ^ n := lt_of_lt_of_le hfinal (pow_lt_pow_left₀ hc ht.1 (by omega)).le
      linarith [ht.2]
    have hmem := hub (0) h0mem
    linarith

/-- (b) 唯一性：`y > 0` 且 `y^n = a` 则 `y = sup E`。 -/
theorem pow_eq_unique (ha : 0 < a) (hn2 : 2 ≤ n) {y : ℝ} (hy : 0 < y)
    (hy_eq : y ^ n = a) : y = sSup (E a n) := by
  have hx := sup_pow_eq ha hn2
  have hn0 : 0 < n := lt_of_lt_of_le (by norm_num) hn2
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have h1 : y ^ n < (sSup (E a n)) ^ n := pow_lt_pow_left₀ hlt hy.le hn0.ne'
    rw [hy_eq, hx] at h1
    exact absurd h1 (lt_irrefl _)
  · have h1 : (sSup (E a n)) ^ n < y ^ n :=
      pow_lt_pow_left₀ hgt (sup_pos ha hn0).le hn0.ne'
    rw [hy_eq, hx] at h1
    exact absurd h1 (lt_irrefl _)

end AnalysisHW1.Problem11
