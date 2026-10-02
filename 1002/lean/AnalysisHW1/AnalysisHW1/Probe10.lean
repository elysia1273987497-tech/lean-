import Mathlib

-- 探查 P10 需要的 API
#check LaurentSeries
#check RatFunc
#check HahnSeries
#check @HahnSeries.leadingCoeff
#check @LaurentSeries.leadingCoeff
#check @LaurentSeries.single
#check @HahnSeries.single
#check @RatFunc.X
#check @Polynomial.X
#check @HahnSeries.order

-- 有没有 order/positivity 实例
example : LinearOrder (LaurentSeries ℚ) := inferInstance
