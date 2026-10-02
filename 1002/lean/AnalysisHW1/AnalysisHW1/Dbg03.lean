import Mathlib

namespace Dbg03

-- 1) LinearOrderedField 是否可用
example {F : Type*} [LinearOrderedField F] (x : F) : x ≤ x := le_refl x

-- 2) abs 相关引理名
example {F : Type*} [LinearOrderedField F] (x : F) : |x| = max x (-x) := abs_eq_max_neg

-- 3) 乘法绝对值
example {F : Type*} [LinearOrderedField F] (x y : F) : |x * y| = |x| * |y| := abs_mul x y

-- 4) 三角不等式
example {F : Type*} [LinearOrderedField F] (x y : F) : |x + y| ≤ |x| + |y| := abs_add x y

-- 5) 反向三角不等式
example {F : Type*} [LinearOrderedField F] (x y : F) : ||x| - |y|| ≤ |x - y| := abs_sub_abs_le_abs_sub x y

-- 6) 从公理出发：|x| = max x (-x) 的两条投影
example {F : Type*} [LinearOrderedField F] (x : F) : x ≤ max x (-x) := le_max_left _ _

-- 7) max 的情形分析
example {F : Type*} [LinearOrderedField F] (x y : F) : max x y = x ∨ max x y = y := max_cases x y |>.imp (fun h => h.1) (fun h => h.1)

end Dbg03
