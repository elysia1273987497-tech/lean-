import Mathlib

namespace Dbg01h

def R (a b : ℤ) : Prop := a ^ 2 = b ^ 2

-- 用「展开 R 与 lambda」的方式避免 rw 匹配问题
-- 先验证：符号不匹配的情形要用 c + d = -c + d 的形式
example {b d : ℤ} : (b - d) ^ 2 = (b + d) ^ 2 - 4 * b * d := by ring

-- 四情形：直接用 subst + ring
example {a b c d : ℤ} (h : a = b) (h' : c = -d) : (a + c) ^ 2 = (b + d) ^ 2 := by
  subst h
  have : c = -d := h'
  rw [this]
  ring

example {a b c d : ℤ} (h : a = -b) (h' : c = d) : (a + c) ^ 2 = (b + d) ^ 2 := by
  subst h
  rw [h']
  ring

example {a b c d : ℤ} (h : a = b) (h' : c = d) : (a + c) ^ 2 = (b + d) ^ 2 := by
  subst h; rw [h']

example {a b c d : ℤ} (h : a = -b) (h' : c = -d) : (a + c) ^ 2 = (b + d) ^ 2 := by
  subst h; rw [h']; ring

end Dbg01h
