import Mathlib

namespace Dbg07v

-- 直接测 linarith 的最小情形
example {a b : ℝ} (h : 1 < b - a) (h2 : a ≤ b - 1) : False := by linarith

end Dbg07v
