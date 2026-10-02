/-
# Problem 1. 等价类与良定义运算

在 `ℤ` 上定义 `a ~ b ↔ a^2 = b^2`，记 `[a]` 为 `a` 的等价类。

(a) 证明 `~` 是等价关系，并描述每个等价类：`[a] = {a, -a}`。

(b) 判断 `[a] ⊕ [b] = [a+b]` 与 `[a] ⊙ [b] = [ab]` 是否良定义。

**结论（与手写解答一致）**：`⊕`（加法）**不**良定义，`⊙`（乘法）**良**定义。

反例取 `a = b = 1`、`c = d = -1`（此时 `a ~ b`、`c ~ d` 均成立）：
`a + c = 0`、`b + d = 2`，而 `0^2 = 0 ≠ 4 = 2^2`，故 `[a+c] ≠ [b+d]`。
手写解答给的是 `[5] ⊕ [5] = [10]` 与 `[5] ⊕ [-5] = [0]`，也一并形式化了。
-/
import Mathlib

namespace AnalysisHW1.Problem01

/-- 题目中的等价关系：`a ~ b ↔ a^2 = b^2`。 -/
def R (a b : ℤ) : Prop := a ^ 2 = b ^ 2

/-- 一个二元运算关于 `~` 良定义。 -/
def WellDefined (f : ℤ → ℤ → ℤ) : Prop :=
  ∀ a b c d : ℤ, R a b → R c d → R (f a c) (f b d)

/-- 加法作为函数，避免 `(· + ·)` 记法在隐式参数上产生意外的 lambda。 -/
def addFun : ℤ → ℤ → ℤ := fun x y => x + y

/-! ## (a) `~` 是等价关系，且 `[a] = {a, -a}` -/

/-- (a) 第一步：`~` 是等价关系。 -/
theorem r_equivalence : Equivalence R :=
  ⟨fun _ => rfl, fun h => h.symm, fun hab hbc => hab.trans hbc⟩

/-- (a) 第二步：两个整数平方相等当且仅当它们相等或互为相反数。 -/
theorem sq_eq_sq_iff (a b : ℤ) : a ^ 2 = b ^ 2 ↔ (a = b ∨ a = -b) := by
  have hfac : a ^ 2 - b ^ 2 = (a - b) * (a + b) := by ring
  rw [← sub_eq_zero, hfac, mul_eq_zero, sub_eq_zero, add_eq_zero_iff_eq_neg]

/-- (a) 第三步：等价类恰好是 `{a, -a}`。 -/
theorem class_eq (a : ℤ) : {b | R a b} = ({a, -a} : Set ℤ) := by
  ext b
  simp only [R, Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · intro h
    -- `h : a^2 = b^2`；倒转后用 `sq_eq_sq_iff b a` 得到 `b = a ∨ b = -a`
    rcases (sq_eq_sq_iff b a).mp h.symm with h' | h'
    · exact Or.inl h'
    · exact Or.inr h'
  · intro h
    -- `h : b = a ∨ b = -a`，反推 `b^2 = a^2`
    rcases h with h | h
    · rw [h]
    · rw [h]; ring

/-- (a) 第四步（手写解答用 `|a|` 表述的同一结论）：`[a] = [|a|]`。 -/
theorem class_abs (a : ℤ) : {b | R a b} = {b | R (|a|) b} := by
  rw [class_eq a, class_eq (|a|)]
  rcases le_total 0 a with ha | ha
  · rw [abs_of_nonneg ha]
  · rw [abs_of_nonpos ha]
    ext b
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, neg_neg]
    tauto

/-! ## (b) `⊕` 不良定义，`⊙` 良定义 -/

/-- (b) `⊕`（加法）**不**良定义。

反例：`a = b = 1`、`c = d = -1`，得 `a + c = 0`、`b + d = 2`，
而 `0^2 = 0 ≠ 4 = 2^2`。 -/
theorem add_not_wellDefined : ¬ WellDefined addFun := by
  intro h
  have hbad : R (addFun 1 (-1)) (addFun 1 1) :=
    h (a := (1 : ℤ)) (b := (1 : ℤ)) (c := (-1 : ℤ)) (d := (1 : ℤ))
      (show R (1 : ℤ) 1 from rfl) (show R (-1 : ℤ) (-1) from rfl)
  unfold R addFun at hbad
  norm_num at hbad

/-- (b) 手写解答的反例同样有效：`[5] ⊕ [5] = [10]` 与 `[5] ⊕ [-5] = [0]` 不同类。 -/
theorem handwritten_counterexample_add : ¬ R (5 + 5) (5 + (-5)) := by
  unfold R; norm_num

/-- (b) `⊙`（乘法）**良**定义。

这一步手写解答完全没有做（它只讨论了 `⊕`）：把 `a^2 = b^2`、`c^2 = d^2`
化为符号关系，四种符号组合逐一验证 `(ac)^2 = (bd)^2`。 -/
theorem mul_wellDefined : WellDefined (fun x y : ℤ => x * y) := by
  intro a b c d hab hcd
  have h1 : a = b ∨ a = -b := (sq_eq_sq_iff a b).mp hab
  have h2 : c = d ∨ c = -d := (sq_eq_sq_iff c d).mp hcd
  unfold R
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> rw [h1, h2] <;> ring

end AnalysisHW1.Problem01
