/-
# Problem 7. 每个区间内的有理数与无理数

设 `a < b` 是实数。

(a) 对每个满足 `n(b-a) > 1` 的 `n ∈ ℕ*`，存在整数 `m` 使 `a < m/n < b`；由此推出 `ℚ` 在 `ℝ` 中稠密。
(b) 仅用 (a) 与 `√2` 的无理性，证明 `(a,b)` 含无穷多个无理数。

## 本版本 Mathlib 的适配要点（都是实际踩到的坑）

* `Nat.exists_pow_gt` 不存在，取 `n` 用 `exists_nat_gt`。
* `rw [lt_div_iff₀ _]` 后目标里的乘积写成 `a * ↑n`（而非 `↑n * a`），要 `mul_comm` 对齐。
* `Irrational x` 即 `x ∉ Set.range Rat.cast`；`intro hmem` 后是集合成员关系，
  此时隐式参数推断易失败，改为手写有理数见证喂 `irrational_sqrt_two`。
* **`linarith` 看不见 `⌊b⌋` 的整数性**（它不把取整当"整数±1"用），
  凡是要用「`a < ⌊b⌋` ⇒ `⌊b⌋ ≤ a + 1`」的地方都必须显式用 `Int.le_floor` / `Int.floor_mono`。
-/
import Mathlib

namespace AnalysisHW1.Problem07

/-! ## (a) 稠密性 -/

/-- (a) 辅助：`b - a > 1` 时区间 `(a, b)` 中有整数，见证取 `m = ⌊b⌋`。

* `a < ⌊b⌋`：若 `⌊b⌋ ≤ a`，则 `b < ⌊b⌋ + 1 ≤ a + 1`，即 `b - a < 1`，与 `h` 矛盾。
* `⌊b⌋ < b`：反证。若 `b ≤ ⌊b⌋`，由**取整的整数性**得 `b - 1 < ⌊b⌋`，
  于是 `b - 1 < ⌊b⌋ ≤ b` 给出 `⌊b⌋ ≤ a + 1`（用 `Int.le_floor`），从而 `b ≤ a + 1`，
  与 `h` 矛盾。

（手写解答只说"至少有一个整数，取出即可"；这里给出取法与验证。） -/
theorem exists_int_between_one {a b : ℝ} (h : 1 < b - a) :
    ∃ m : ℤ, a < (m : ℝ) ∧ (m : ℝ) < b := by
  have hgt : a < (⌊b⌋ : ℝ) := by
    by_contra hc
    push_neg at hc
    have hfl : b < (⌊b⌋ : ℝ) + 1 := Int.lt_floor_add_one b
    linarith
  refine ⟨⌊b⌋, hgt, ?_⟩
  by_contra hc
  push_neg at hc
  -- `hc : b ≤ ⌊b⌋`。由 `a < ⌊b⌋` 与整数性得 `⌊b⌋ ≤ a + 1`
  have hle : (⌊b⌋ : ℝ) ≤ a + 1 := by
    apply Int.le_floor.mpr
    push_cast
    by_contra hcon
    push_neg at hcon
    -- `hcon : a + 1 < ⌊b⌋`，与 `⌊b⌋ ≤ b` 给出 `b - a > 1` 的另一写法，矛盾
    have hbl : (⌊b⌋ : ℝ) ≤ b := Int.floor_le b
    linarith
  have : b ≤ a + 1 := le_trans hc hle
  linarith

/-- (a) 主结论：满足 `n(b-a) > 1` 时存在整数 `m` 使 `a < m/n < b`。

见证取 `m = ⌊n*b⌋ - 1`：由 `n(b-a) > 1` 得 `n*a + 1 < n*b`，
故 `Int.le_floor` 给出 `n*a + 1 ≤ ⌊n*b⌋`，即 `n*a < ⌊n*b⌋ - 1`；
又 `⌊n*b⌋ ≤ n*b`，故 `⌊n*b⌋ - 1 + 1 ≤ n*b`，两边除 `n` 得严格小于 `b`。 -/
theorem exists_int_div_between {a b : ℝ} (_hab : a < b) {n : ℕ} (hn : 0 < n)
    (h : 1 < (n : ℝ) * (b - a)) : ∃ m : ℤ, a < (m : ℝ) / n ∧ (m : ℝ) / n < b := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h1 : (n : ℝ) * a + 1 < (n : ℝ) * b := by linarith
  -- 关键一：`n*a + 1 ≤ ⌊n*b⌋`
  have hle : ((n : ℝ) * a + 1) ≤ ((⌊(n : ℝ) * b⌋ : ℤ) : ℝ) := by
    apply Int.le_floor.mpr
    exact_mod_cast le_of_lt h1
  have hfl_le : ((⌊(n : ℝ) * b⌋ : ℤ) : ℝ) ≤ (n : ℝ) * b := Int.floor_le _
  refine ⟨⌊(n : ℝ) * b⌋ - 1, ?_, ?_⟩
  · -- `a < (⌊n*b⌋ - 1)/n`
    rw [lt_div_iff₀ hn']
    push_cast
    linarith
  · -- `(⌊n*b⌋ - 1)/n < b`
    rw [div_lt_iff₀ hn']
    push_cast
    linarith

/-- (a) 稠密性：任意 `a < b` 之间都有有理数。 -/
theorem exists_rat_between {a b : ℝ} (hab : a < b) : ∃ q : ℚ, a < (q : ℝ) ∧ (q : ℝ) < b := by
  have hb : 0 < b - a := by linarith
  obtain ⟨k, hk⟩ := exists_nat_gt (1 / (b - a))
  have hnk : 1 < (k : ℝ) * (b - a) := by
    rw [div_lt_iff₀ hb] at hk
    linarith
  have hkpos : 0 < k := by
    by_contra h
    push_neg at h
    have h0 : k = 0 := Nat.le_zero.mp h
    subst h0
    norm_num at hnk
  obtain ⟨m, hm1, hm2⟩ := exists_int_div_between hab hkpos hnk
  exact ⟨m / k, by push_cast; exact hm1, by push_cast; exact hm2⟩

/-! ## (b) 每个区间含无穷多个无理数 -/

/-- `√2` 的无理性（Mathlib 已有）。 -/
theorem sqrt_two_irrational : Irrational (Real.sqrt 2) := irrational_sqrt_two

/-- (b) 辅助：非零有理数乘 `√2` 是无理数。 -/
theorem rat_mul_sqrt_two_irrational {c : ℚ} (hc : c ≠ 0) :
    Irrational ((c : ℝ) * Real.sqrt 2) := by
  intro hmem
  obtain ⟨s, hs⟩ := hmem
  have hcR : (c : ℝ) ≠ 0 := by exact_mod_cast hc
  have hs' : Real.sqrt 2 * (c : ℝ) = (s : ℝ) := by
    rw [mul_comm]; exact hs.symm
  have hval : Real.sqrt 2 = (s : ℝ) / (c : ℝ) := by
    rw [eq_div_iff hcR]; exact hs'
  have hcast : (((s / c : ℚ) : ℝ)) = (s : ℝ) / (c : ℝ) := by push_cast; ring
  exact sqrt_two_irrational ⟨s / c, by rw [hcast, hval]⟩

/-- (b) 辅助：有理数 + 无理数 = 无理数。 -/
theorem irr_rat_add {r : ℚ} {t : ℝ} (ht : Irrational t) : Irrational ((r : ℝ) + t) := by
  intro hrat
  obtain ⟨s, hs⟩ := hrat
  exact ht ⟨s - r, by push_cast; linarith [hs]⟩

/-- (b) 辅助：`√2 / x`（`x` 为非零有理数）是无理数。 -/
theorem sqrt_two_div_rat_irrational {x : ℚ} (hx : x ≠ 0) :
    Irrational (Real.sqrt 2 / (x : ℝ)) := by
  have hxR : (x : ℝ) ≠ 0 := by exact_mod_cast hx
  have hrew : Real.sqrt 2 / (x : ℝ) = ((x⁻¹ : ℚ) : ℝ) * Real.sqrt 2 := by
    rw [Rat.cast_inv]
    field_simp
  rw [hrew]
  exact rat_mul_sqrt_two_irrational (inv_ne_zero hx)

/-- (b) 对任意 `a < b`，在 `(a, b)` 中存在无理数。

构造：取有理数 `r ∈ (a, b)`，再取 `n` 使 `√2/n < b - r`，
则 `r + √2/n ∈ (a, b)` 且无理。 -/
theorem exists_irrational_between {a b : ℝ} (hab : a < b) :
    ∃ z : ℝ, a < z ∧ z < b ∧ Irrational z := by
  obtain ⟨r, hr1, hr2⟩ := exists_rat_between hab
  have hbr : (0 : ℝ) < b - r := by linarith
  have hroot_pos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hq_pos : (0 : ℝ) < Real.sqrt 2 / (b - r) := div_pos hroot_pos hbr
  obtain ⟨n, hn⟩ := exists_nat_gt (Real.sqrt 2 / (b - r))
  have hnpos : 0 < n := by
    by_contra h
    push_neg at h
    have h0 : n = 0 := Nat.le_zero.mp h
    subst h0
    norm_num at hn
    exact absurd hn (not_lt.mpr hq_pos.le)
  have hn' : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hineq : Real.sqrt 2 / n < b - r := by
    rw [div_lt_iff₀ hbr] at hn
    rw [div_lt_iff₀ hn']
    linarith
  have hpos : (0 : ℝ) < Real.sqrt 2 / n := div_pos hroot_pos hn'
  have hz_gt : a < (r : ℝ) + Real.sqrt 2 / n := by linarith
  have hz_lt : (r : ℝ) + Real.sqrt 2 / n < b := by linarith
  have hirr : Irrational (Real.sqrt 2 / n) := by
    have hrew : Real.sqrt 2 / (n : ℝ) = ((n : ℚ)⁻¹ : ℚ) * Real.sqrt 2 := by
      push_cast
      field_simp
    rw [hrew]
    exact rat_mul_sqrt_two_irrational (by
      simp only [ne_eq, inv_eq_zero]
      exact_mod_cast (Nat.pos_iff_ne_zero.mp hnpos))
  exact ⟨_, hz_gt, hz_lt, irr_rat_add hirr⟩

/-- (b) 模型函数：`F n = a + (b - a)·(n + √2)/(n + 2)`。 -/
noncomputable def F (a b : ℝ) (n : ℕ) : ℝ :=
  a + (b - a) * (((n : ℝ) + Real.sqrt 2) / ((n : ℝ) + 2))

theorem F_apply (a b : ℝ) (n : ℕ) :
    F a b n = a + (b - a) * (((n : ℝ) + Real.sqrt 2) / ((n : ℝ) + 2)) := rfl

/-- (b) 区间 `(a,b)` 中有无穷多个无理数。

**构造**：`F n = a + (b - a)·(n + √2)/(n + 2)`。

* `a < F n < b`：`0 < (n+√2)/(n+2) < 1`（后者等价于 `√2 < 2`）且 `b > a`。
* **严格递增** ⇒ 单射：`F n - F m = (b-a)(n-m)(2-√2)/((m+2)(n+2)) > 0`。
* 无理：`F n = [a + (b-a)·n/(n+2)] + [(b-a)/(n+2)]·√2`，
  前项有理，后项系数是非零有理数乘 `√2`。 -/
theorem infinite_irrationals_between {a b : ℝ} (hab : a < b) :
    ∃ f : ℕ → ℝ, (∀ n, a < f n ∧ f n < b ∧ Irrational (f n)) ∧ Function.Injective f := by
  have hba : (0 : ℝ) < b - a := by linarith
  have hroot_lt : Real.sqrt 2 < 2 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
  have hden : ∀ n : ℕ, (0 : ℝ) < (n : ℝ) + 2 := fun n => by positivity
  have hq_pos : ∀ n : ℕ, (0 : ℝ) < ((n : ℝ) + Real.sqrt 2) / ((n : ℝ) + 2) :=
    fun n => div_pos (by positivity) (hden n)
  have hq_lt_one : ∀ n : ℕ, ((n : ℝ) + Real.sqrt 2) / ((n : ℝ) + 2) < 1 := by
    intro n
    rw [div_lt_one (hden n)]
    linarith
  have hF_mono : ∀ m n : ℕ, m < n → F a b m < F a b n := by
    intro m n hmn
    have hmn' : (m : ℝ) < (n : ℝ) := by exact_mod_cast hmn
    have hkey : ((n : ℝ) + Real.sqrt 2) / ((n : ℝ) + 2) -
        ((m : ℝ) + Real.sqrt 2) / ((m : ℝ) + 2) =
        ((n : ℝ) - (m : ℝ)) * (2 - Real.sqrt 2) /
          (((m : ℝ) + 2) * ((n : ℝ) + 2)) := by
      field_simp
      ring
    have hpos : 0 < ((n : ℝ) + Real.sqrt 2) / ((n : ℝ) + 2) -
        ((m : ℝ) + Real.sqrt 2) / ((m : ℝ) + 2) := by
      rw [hkey]
      exact div_pos (by nlinarith) (by positivity)
    rw [F_apply, F_apply]
    nlinarith
  have hF_irr : ∀ n : ℕ, Irrational (F a b n) := by
    intro n
    rw [F_apply]
    have hsplit : a + (b - a) * (((n : ℝ) + Real.sqrt 2) / ((n : ℝ) + 2)) =
        (a + (b - a) * ((n : ℝ) / ((n : ℝ) + 2))) +
          ((b - a) / ((n : ℝ) + 2)) * Real.sqrt 2 := by
      field_simp
      ring
    rw [hsplit]
    have hirr : Irrational (((b - a) / ((n : ℝ) + 2)) * Real.sqrt 2) := by
      obtain ⟨c, hc⟩ : ∃ c : ℚ, (c : ℝ) = (b - a) / ((n : ℝ) + 2) := by
        refine ⟨_, ?_⟩
        push_cast
        ring
      rw [← hc]
      refine rat_mul_sqrt_two_irrational ?_
      rw [Rat.cast_ne_zero, ← hc]
      exact div_ne_zero (ne_of_gt hba) (ne_of_gt (hden n))
    have hrat : ∃ r : ℚ, (r : ℝ) = a + (b - a) * ((n : ℝ) / ((n : ℝ) + 2)) := by
      refine ⟨_, ?_⟩
      push_cast
      ring
    obtain ⟨r, hr⟩ := hrat
    rw [← hr]
    exact irr_rat_add hirr
  refine ⟨F a b, ?_, ?_⟩
  · intro n
    exact ⟨by have := hq_pos n; rw [F_apply]; nlinarith,
           by have := hq_lt_one n; rw [F_apply]; nlinarith,
           hF_irr n⟩
  · intro m n hmn
    rcases lt_trichotomy m n with hlt | heq | hgt
    · exact absurd (hmn ▸ hF_mono m n hlt) (lt_irrefl _)
    · exact heq
    · exact absurd (hmn.symm ▸ hF_mono n m hgt) (lt_irrefl _)

end AnalysisHW1.Problem07
