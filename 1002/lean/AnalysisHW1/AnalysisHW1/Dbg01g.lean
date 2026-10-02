import Mathlib

namespace Dbg01g

-- 用 simp only [h, h'] 做替换，再 ring
example {a b c d : ℤ} (h : a = b) (h' : c = d) : (a + c) ^ 2 = (b + d) ^ 2 := by
  simp only [h, h']

example {a b c d : ℤ} (h : a = b) (h' : c = -d) : (a + c) ^ 2 = (b + d) ^ 2 := by
  simp only [h, h']; ring

example {a b c d : ℤ} (h : a = -b) (h' : c = d) : (a + c) ^ 2 = (b + d) ^ 2 := by
  simp only [h, h']; ring

example {a b c d : ℤ} (h : a = -b) (h' : c = -d) : (a + c) ^ 2 = (b + d) ^ 2 := by
  simp only [h, h']; ring

-- rw 版本对照
example {a b c d : ℤ} (h : a = -b) (h' : c = -d) : (a + c) ^ 2 = (b + d) ^ 2 := by
  rw [h, h']; ring

end Dbg01g
