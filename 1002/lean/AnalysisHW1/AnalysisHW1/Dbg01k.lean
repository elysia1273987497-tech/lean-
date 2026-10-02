import Mathlib

namespace Dbg01k

def R (a b : ℤ) : Prop := a ^ 2 = b ^ 2

-- 最小化：(2:ℤ)^2 = (-2:ℤ)^2 到底能不能证？
example : (2 : ℤ) ^ 2 = ((-2 : ℤ)) ^ 2 := by norm_num
example : ((-1 : ℤ) + (-1)) = (-2 : ℤ) := by norm_num
example : ((1 : ℤ) + 1) = 2 := by norm_num
example : R ((1 : ℤ) + 1) ((-1 : ℤ) + (-1)) := by unfold R; norm_num
example : ¬ (R ((1 : ℤ) + 1) ((-1 : ℤ) + (-1))) := by unfold R; norm_num

end Dbg01k
