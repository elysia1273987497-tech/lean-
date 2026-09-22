def sum_of_powers (power : Nat -> Nat) (a : Nat) (b : Nat) : Nat := power a + power b
def square (n : Nat) : Nat :=n * n
#check sum_of_powers
--参数1是一个函数类型（Nat->Nat），参数2和参数3是两个自然数(Nat)，返回值是一个自然数(Nat)
--
#check square
def sum_of_squares (a : Nat) (b : Nat) : Nat := sum_of_powers square a b
#eval sum_of_squares 3 4                 
--函数嵌套的想法
def apply_twice (f : Int -> Int) (x : Int) : Int := f (f x)
def add10 (n : Int) : Int := n + 10
def add100 (n : Int) : Int := n + 100
#eval apply_twice add10 10
def compose (f : Int -> Int) (g : Int -> Int) (x : Int) : Int := f (g (x))
#eval compose add100 add10 10
#check compose
def abs (n : Int) : Int := if n >=0 then n else if n < 0 then -n else 0
#check abs
#eval compose abs add10 (-20) --负数一定要加上括号
def sign (n : Int) : Int := if n > 0 then 1 else if n < 0 then -1 else 0
#check sign                   --必须用else结尾 
def fact (n : Nat) : Nat :=
  match n with
  | 0 =>1
  | k + 1 => (k + 1) * fact k --不要用重复字母！
def fib (n : Nat) : Nat :=
  match n with
  |0 =>0
  |1 =>1
  |k+2 => fib k + fib (k + 1)
#eval fib 10
#check fib
--看一个双重归纳的例子
def add (n : Nat) (m : Nat) : Nat :=
  match m with
  | 0 => n
  | k + 1 => add (n + 1) k--严格的定义了加法，所以数学还是有点的用的（bushi
--递归函数在计算中反复调用自身（类似归纳定义）
--test（gcd）

def gcd (n k : Nat) : Nat :=
  match k with
  | 0 => n
  | k + 1 => gcd (k + 1) (n % (k + 1))
  termination_by k--声明终止度量
  decreasing_by exact Nat.mod_lt n (Nat.succ_pos k)--用这个定理来严格证明确实会终止
--test(power)
def power (n : Nat) (m : Nat): Nat :=
  match m with
  | 0 => 1
  | k + 1 => power (n) (k) * n
def fact_aux (n : Nat) (acc : Nat) : Nat :=
  match n with
  |0 => acc
  |k + 1 => fact_aux k ((k+1) * acc)--实测发现正常递归计算12000会有困难，尾递归可以轻松计算20000的阶乘
--方便使用，做一个嵌套
def factTail ( n : Nat ) : Nat := fact_aux n 1
--test(fib_aux)
def fib_aux (n cu_1 cu_2 : Nat) : Nat :=
  match n with 
  |0 => cu_2
  |1 => cu_1
  |k + 1 => fib_aux (k) (cu_1 + cu_2) (cu_1)--令人震惊的结果，用初版本差不多1000就会卡顿，尾递归后甚至能轻松完成100000的情况




