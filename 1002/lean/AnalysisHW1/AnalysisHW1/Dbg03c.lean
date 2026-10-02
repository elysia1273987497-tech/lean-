import Mathlib

#check @abs_add_le
#check @abs_eq_max_neg
#check @abs_mul
#check @abs_sub_abs_le_abs_sub
#check IsOrderedRing
#check IsStrictOrderedRing

-- 试着组合出"有序域"
example {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F] (x y : F) :
    |x + y| ≤ |x| + |y| := abs_add_le x y

example {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F] (x y : F) :
    |x * y| = |x| * |y| := abs_mul x y

example {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F] (x : F) :
    |x| = max x (-x) := abs_eq_max_neg

example {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F] (x y : F) :
    ||x| - |y|| ≤ |x - y| := abs_sub_abs_le_abs_sub x y
