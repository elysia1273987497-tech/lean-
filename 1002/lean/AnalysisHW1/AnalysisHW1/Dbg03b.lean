import Mathlib

-- 直接问 Lean
#check LinearOrderedField
#check @abs_eq_max_neg
#check @abs_mul
#check @abs_add
#check @abs_sub_abs_le_abs_sub
#check @le_max_left
#check @max_cases

example {F : Type*} [LinearOrderedField F] (x : F) : x ≤ x := le_refl x
