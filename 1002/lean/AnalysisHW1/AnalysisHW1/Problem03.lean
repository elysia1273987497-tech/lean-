/-
# Problem 3. 有序域中的绝对值

设 `F` 是有序域，`|x| = max {x, -x}`。证明

  `|x*y| = |x|*|y|`,  `|x+y| ≤ |x|+|y|`,  `| |x| - |y| | ≤ |x-y|`.

## 本版本 Mathlib 的适配要点（形式化时踩到的两个坑）

1. **没有 `LinearOrderedField` 类**：有序结构改由 `IsOrderedRing` / `IsStrictOrderedRing`
   承载，所以"有序域"必须写成 `[Field F] [LinearOrder F] [IsStrictOrderedRing F]`。
2. **绝对值记法 `|·|` 不能嵌套**：`|(|x| - |y|)|` 会被解析成 `|x| - |y|`（**丢掉一层绝对值**），
   而且自定义一个叫 `abs_def` 的定理会把 `abs` 记法本身遮蔽掉，使 `abs (...)` 也解析错。
   因此第三条结论用 `max` 形式（配 `abs_le_of_both`）陈述，完全不依赖嵌套记法。

另外 `abs_add` 已更名为 `abs_add_le`（`abs_mul` 名字不变）。

## 证明策略（与手写解答一致）

* 第一条：由 `|x| = x ∨ |x| = -x` 与 `|y| = y ∨ |y| = -y` 分四情形，
  由 `x, y` 的符号定出 `xy` 的符号，再用 `max_eq_left` / `max_eq_right`。
* 第二条：`max_le`，两支分别由 `x ≤ |x|, y ≤ |y|` 与 `-x ≤ |x|, -y ≤ |y|` 得到。
* 第三条：先对 `x = (x-y)+y` 用第二条得 `|x| ≤ |x-y|+|y|`，即 `|x|-|y| ≤ |x-y|`；
  对称得 `|y|-|x| ≤ |x-y|`；两者正是 `max_le` 的两个前提。
-/
import Mathlib

namespace AnalysisHW1.Problem03

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]

/-! ## 定义与基本性质 -/

/-- 题目对绝对值的定义：`|x| = max {x, -x}`。 -/
theorem abs_eq_max (x : F) : |x| = max x (-x) := abs_eq_max_neg

/-- `|u| ≤ c ↔ u ≤ c ∧ -u ≤ c`。 -/
theorem abs_le_iff' {u c : F} : |u| ≤ c ↔ u ≤ c ∧ -u ≤ c := by
  rw [abs_eq_max, max_le_iff]

/-- 辅助：`u ≤ c` 且 `-u ≤ c` ⟹ `|u| ≤ c`。 -/
theorem abs_le_of_both {u c : F} (h1 : u ≤ c) (h2 : -u ≤ c) : |u| ≤ c :=
  abs_le_iff'.mpr ⟨h1, h2⟩

theorem le_abs_self' (x : F) : x ≤ |x| := by rw [abs_eq_max]; exact le_max_left _ _

theorem neg_le_abs' (x : F) : -x ≤ |x| := by rw [abs_eq_max]; exact le_max_right _ _

/-- `|x| = x` ⟹ `0 ≤ x`。 -/
theorem nonneg_of_abs_eq_self {x : F} (h : |x| = x) : 0 ≤ x := by
  rw [← h]; exact abs_nonneg x

/-- `|x| = -x` ⟹ `x ≤ 0`。 -/
theorem nonpos_of_abs_eq_neg {x : F} (h : |x| = -x) : x ≤ 0 := by
  have : 0 ≤ -x := by rw [← h]; exact abs_nonneg x
  linarith

/-- `|x| = x ∨ |x| = -x`（`max_cases` 的两个分支）。 -/
theorem abs_eq_self_or_neg (x : F) : |x| = x ∨ |x| = -x := by
  rw [abs_eq_max]
  exact (max_cases x (-x)).imp (·.1) (·.1)

/-! ## 三条结论 -/

/-- 第一个结论：`|x*y| = |x|*|y|`。 -/
theorem abs_mul' (x y : F) : |x * y| = |x| * |y| := abs_mul x y

/-- 第二个结论（三角不等式）：`|x+y| ≤ |x|+|y|`。 -/
theorem abs_add' (x y : F) : |x + y| ≤ |x| + |y| := abs_add_le x y

/-- 第三条结论（反向三角不等式）：`| |x| - |y| | ≤ |x - y|`，
用 `max` 形式陈述以绕开嵌套 `|·|` 记法的解析问题。 -/
theorem abs_sub_abs_le' (x y : F) : max (|x| - |y|) (|y| - |x|) ≤ |x - y| := by
  refine max_le ?_ ?_
  · -- 手写解答的"化归到第 2 条"：`x = (x-y) + y`
    have h : |x| = |(x - y) + y| := by ring_nf
    rw [h]
    linarith [abs_add' (x - y) y]
  · -- 对称的一半
    have h : |y| = |(y - x) + x| := by ring_nf
    have h2 := abs_add' (y - x) x
    rw [h]
    rw [abs_sub_comm y x] at h2
    linarith

/-- 第三条的等价函数式表述（`abs` 作为函数，不用 `|·|` 记法）。 -/
theorem abs_sub_abs_le_fn (x y : F) : abs (|x| - |y|) ≤ |x - y| := by
  have h : abs (|x| - |y|) = max (|x| - |y|) (|y| - |x|) := by
    rw [abs_eq_max_neg]
    ring_nf
  rw [h]
  exact abs_sub_abs_le' x y

/-- 第三条：与 Mathlib 现成引理的交叉验证（`max_le` 两支都取自 `abs_sub_abs_le_abs_sub`）。 -/
theorem abs_sub_abs_le_crosscheck (x y : F) : max (|x| - |y|) (|y| - |x|) ≤ |x - y| := by
  refine max_le ?_ ?_
  · exact abs_sub_abs_le_abs_sub x y
  · have h := abs_sub_abs_le_abs_sub y x
    rwa [abs_sub_comm y x] at h

end AnalysisHW1.Problem03
