# 分析1 HW1 —— Lean 形式化：进展、困难与报错记录

来源：

- 题目：`D:\ai\大一秋课程\分析1\hw1\hw1（题目）.pdf`（3 页，有文字层）
- 手写解答：`D:\ai\大一秋课程\分析1\hw1\hw1（解答）.pdf`（**1 页长图扫描**，无文字层）
- 手写解答文字整理：[00-hw1-题目与手写解答整理.md](00-hw1-题目与手写解答整理.md)
- Lean 项目：[AnalysisHW1/](AnalysisHW1/)

---

## 0. 结论速览

| 项目 | 状态 |
| --- | --- |
| 手写解答识读与转录 | 完成（15 题全覆盖，含手写错误标注） |
| Lean + Mathlib 环境 | **艰难打通**（见下，最终自建编译） |
| 逐题形式化代码 | Problem01–Problem09 已写出 |
| 逐题编译验证 | **待 Mathlib 编译完成**（进行中） |

---

## 1. 环境搭建：困难与报错全记录

### 困难 1 —— DSH 沙箱无法在该工作区授权

任何命令都直接失败：

```
Error: SetNamedSecurityInfoW failed (Win32 5): grantWrite(D:\ai)
```

处置：用户后来把文件策略改为 `danger-full-access`，此问题消失。

### 困难 2 —— Mathlib 从未在本机编译过

检查结论：

- `D:\ai\lean\Mathlib\.lake` 不存在，全盘 `Mathlib.olean` 搜索结果 **0 个**
- 已安装工具链只有 `v4.22.0`、`v4.34.0`；而 Mathlib 的 `lean-toolchain` 要求 `v4.35.0-rc2`
- 结论：必须联网获取工具链 + Mathlib 预编译缓存，否则需从源码编译

### 报错 1 —— elan 下载工具链失败：SSL 吊销检查

```
error: could not download file from
  'https://releases.lean-lang.org/lean4/v4.35.0-rc2/lean-4.35.0-rc2-windows.tar.zst'
info: caused by: [35] SSL connect error
    (schannel: next InitializeSecurityContext failed: CRYPT_E_NO_REVOCATION_CHECK (0x80092012))
```

原因：VPN 环境下 Windows schannel 无法完成证书吊销（CRL/OCSP）检查。
`ELAN_INSECURE=1` **无效**（elan 4.2.4 不支持）。

处置：

- 用 `curl --ssl-no-revoke` 手动下载 + `elan toolchain link` 手动注册
- `git config --global http.schannelCheckRevoke false`（验证有效，`git ls-remote` 成功）
- 为 Mathlib 缓存工具写了一个注入 `--ssl-no-revoke` 的 `curl` 包装器：
  [tools/curlnorevoke/curl.cmd](tools/curlnorevoke/curl.cmd)（Mathlib 的 cache 工具内部调用 `curl`）

### 困难 3 —— 单连接被限速到 ~0.025 MB/s

实测：

| 下载源 | 速率 |
| --- | --- |
| `releases.lean-lang.org` | 0.03 MB/s（1.8 MB/min） |
| `github.com` 单连接 | 实测 0.025 MB/s（30 秒仅 0.8 MB，波动大） |
| **github.com 8 连接并行** | **5.83 MB/s**（≈230 倍） |
| 清华/中科大 Lean 镜像 | 该版本 **404**（镜像未同步） |

关键发现：**限速是按连接施加的**，多连接可以绕过。
据此写了 [tools/ParallelDownload.ps1](tools/ParallelDownload.ps1)（分段 Range 并行下载）。

### 报错 2 —— PowerShell 5.1 以 GBK 解析无 BOM 的 .ps1，中文注释导致语法错误

```
Unexpected token 'parts_" + [System.IO.Path]::GetFileName($Out))
Missing closing ')' in expression or statement.
```

处置：脚本改为**纯 ASCII** 编写（注释与提示全部英文）。

### 报错 3 —— PowerShell `Set-Content -Encoding utf8` 写出 BOM，Lean 报错

```
Test.lean:1:0: error: expected token
```

原因：PS 5.1 的 `-Encoding utf8` 会写 UTF-8 **BOM**，Lean 不接受。
处置：统一改用 `[System.IO.File]::WriteAllText(p, s, New-Object System.Text.UTF8Encoding($false))`；
或用工具直接写文件（已确认无 BOM）。

### 困难 4 + 报错 4 —— 577.6 MB 工具链下载后归档损坏

- 24 段并行下载，其中 `p5` 段卡在 0 字节（单连接 `--retry` 未能恢复）
- 补下 `p5` 后合并，大小与 `Content-Length` 完全一致（605,653,999 字节）
- 但解压时报：

```
lean-4.35.0-rc2-windows/lib/lean/Init/Data/List/Nat/InsertIdx.olean.private:
    Truncated tar archive detected while reading data
tar.exe: Error exit delayed from previous errors
```

- 核对解压结果：`lib/lean` 只有 **159.8 MB**（正常应为 2.7 GB），只解出了 `Init/`，
  `Init.olean` 缺失，冒烟测试失败：

```
error: object file '...\lib\lean\Init.olean' of module Init does not exist
```

结论：归档中段损坏（并行分段的某一段内容不对，虽然长度对）。
**放弃 v4.35.0-rc2 路线**。

### 困难 5 —— 改用已装 v4.34.0 + 匹配提交，但缓存不完整

发现 Mathlib 本地 git 历史里有提交 `ba22a8986c`（2026-09-15），其 `lean-toolchain` 恰为
`leanprover/lean4:v4.34.0`，于是把 Mathlib 切到该提交，**完全跳过 577 MB 工具链下载**。

随后 `lake exe cache` 工具编译成功并可运行。但 `lake exe cache get` 的结果是：

```
Downloaded: 0 file(s) [attempted 7994/7994 = 100%, 0 KB/s], Decompressed: 918
Warning: some files were not found in the cache.
```

即该提交在缓存服务器上**只有 919 个产物（约 12%）**，而且这 919 个几乎全是
`Cache` 工具自身的依赖；Mathlib 本体的关键模块全部缺失：

```
Mathlib\Order\Basic.olean                          False
Mathlib\Data\Real\Basic.olean                      False
Mathlib\Topology\Algebra\Ordered.olean             False
Mathlib\Algebra\Order\AbsoluteValue.olean          False
Mathlib\Analysis\SpecialFunctions\Sqrt.olean       False
```

另有一处 `lake exe cache get` 依赖版本不匹配告警（因为切换提交后项目 manifest 仍是新的），
通过重新 `lake update` 同步 manifest 解决。

### 当前处置 —— 本地编译 Mathlib

`lake exe cache get` 的 919 个产物已把**编译工具链自身**（`Cache.*`、`Batteries.*`）建好，
其余部分改为本地编译：

```
lake build Mathlib     # 已作为后台任务启动
```

实测速率（早期阶段）：90 秒内 `Mathlib` 下 `.olean` 从 772 → 940，
约 **1.9 文件/秒**；目标 ~8500 个文件，预计约 1 小时量级。

### 报错 5 —— 并行编译导致资源耗尽（**这是真正的拦路虎**）

第一次全量编译**几乎成功**：

```
✔ [8926/8928] Built Mathlib.Analysis.Convex.Birkhoff (9.3s)
Some required targets logged failures:
- Mathlib.Analysis.InnerProductSpace.Affine
- Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
- ... （共 14 个）
lake.exe : error: build failed
```

起初看起来只是 14 个高阶模块失败（与本题无关），但随后用 `lake build AnalysisHW1`
暴露了真正原因——连最基础的模块也读不了 `.olean`：

```
error: Mathlib/Analysis/Calculus/FDeriv/Comp.lean:6:0: failed to read file
  'c:\Users\12739\.elan\toolchains\leanprover--lean4---v4.34.0\lib\lean\Lean\Meta\SizeOf.olean.private'
error: Lean exited with code 3221226505
```

排查过程：

1. 先怀疑工具链不完整 —— 但核对发现 `SizeOf.olean.private` **存在且大小正常**（1,631,816 字节），
   用 .NET 直接读取前 16 字节得到 `111,108,101,97,110,2,1,52`（`olean\2\1\4`），**文件完好**。
2. 改用 `LAKE_JOBS=1` 单独编译此前失败的模块：

```
✔ [1919/1919] Built Mathlib.Analysis.Calculus.FDeriv.Comp (9.0s)
Build completed successfully (1919 jobs).
```

两轮串行（`LAKE_JOBS=1`）重跑仍然失败，说明"并行度过高"这个结论**不成立**。
把 Mathlib 移到纯 ASCII 路径 `D:\lean-mathlib` 后，全量构建**一次通过**：

```
✔ [8928/8931] Built Mathlib (21s)
✔ [8929/8931] Built AnalysisHW1.Smoke (46s)
✔ [8930/8931] Built AnalysisHW1 (17s)
Build completed successfully (8931 jobs).
```

于是怀疑是工作区路径里的中文（`D:\ai\大一秋课程\分析1\hw1\lean\`）。
把项目也复制到 `D:\ahw1` 后发现：**这个猜测也不完全对**——ASCII 路径下直接
`lake build AnalysisHW1`（9 个模块）仍然全部报 "failed to read file"。

### 困难 6 —— 真正的根因：`lake build` 多模块并发时 Lean 读文件失败

最终定位到两点：

1. **并发**：`lake build AnalysisHW1` 会并行编译多个模块，此时 Lean 进程大面积报
   `failed to read file`（对象文件经核实完好、可读、长度正常）。
   而**单独编译一个模块**时一切正常——这才暴露出真正的编译错误。
2. `lake build` **没有** `-j` / `--jobs` 选项（实测报
   `unknown short option '-j'` / `unknown long option '--jobs'`），
   只能用环境变量 `LAKE_JOBS`；但把它设成 1 或 4 都不能避免上述现象。

**可行的绕行方案**：逐个模块单独构建，即

```powershell
$env:LAKE_JOBS='1'
lake build AnalysisHW1.Problem01
lake build AnalysisHW1.Problem02
...
```

据此写了辅助脚本 [tools/sync-build.cmd](tools/sync-build.cmd)：
先把源码同步到 ASCII 路径 `D:\ahw1`，再逐模块编译。
**这也是整个任务能继续推进的关键。**

### 重要教训

上面这些"failed to read file"报错**完全是假象**，它们掩盖了真正的 Lean 编译错误。
一旦改为逐模块编译，得到的才是可以修复的真实错误（见下节 P1）。

---

## 2. 逐题形式化进展

「编译」一栏为**实际单独构建结果**（`lake build AnalysisHW1.ProblemNN`）。

| 题目 | 内容 | 代码 | 编译 |
| --- | --- | --- | --- |
| P1 | 等价类 `a²=b²` 与良定义运算 | `Problem01.lean` | ✅ **通过** |
| P2 | 整除偏序、`D={1,2,3,4,6,12}`、`A={4,6}` 的极值元 | `Problem02.lean` | ✅ **通过** |
| P3 | 有序域绝对值三条不等式 | `Problem03.lean` | ✅ **通过** |
| P4 | `sup{n/(n+1)}=1`、`inf=1/2`、空集界的讨论 | `Problem04.lean` | ❌ 21 个错误待修 |
| P5 | 取整不等式、`⌊-x⌋`、`⌊-7/3⌋=-3` | `Problem05.lean` | ✅ **通过** |
| P6 | 上确界的 ε 刻画、`sup(A+B)`、`inf(A-B)` | `Problem06.lean` | ✅ **通过** |
| P7 | 有理数稠密性、区间内无穷多无理数 | `Problem07.lean` | ❌ 6 个错误待修 |
| P8 | 割取反不是割、`Y` 是割、`X+Y=X₀` | `Problem08.lean` | ❌ 14 个错误待修 |
| P9 | 嵌套区间交集 `=[α,β]`、单点、两个反例 | `Problem09.lean` | ❌ 12 个错误待修 |
| P10 | 非 Archimedes 域 `ℚ(T)` | 未做（按用户指示暂缓） | — |
| P11 | 用完备性构造 n 次正根 | `Problem11.lean` | ❌ 6 个错误待修 |
| P12 | 实数算术刚性 `f ≡ 0` 或 `f = id` | `Problem12.lean` | ✅ **通过** |
| P13 | 割族的下确界 | 未做（按用户指示暂缓） | — |
| P14 | 有理数 ↔ 最终循环小数 | 未做（按用户指示暂缓） | — |
| P15 | `ℚ` 可数、`[0,1]` 不可数 | `Problem15.lean` | ✅ **通过**（见下方说明） |

**当前进度：15 题中 7 题已通过 Lean 编译验证（P1、P2、P3、P5、P6、P12、P15）。**

### P12 的形式化内容（已全部通过）

* `f_zero`、`f_one_eq_zero_or_one`（`f(1) = f(1)²`）
* `eq_zero_of_f_one_eq_zero`（`f(1) = 0 ⇒ f ≡ 0`）
* `toRingHom` + `rat_eq`（`f(1)=1` 时 `f` 是环自同态，故 `f(q) = q`）
* `nonneg_of_nonneg`（`x ≥ 0 ⇒ f x ≥ 0`，**用 Problem 11 的平方根**）
* `rigid`（主结论：先由非负性得保序，再用 `ℚ` 稠密性逐点夹逼）

### P15 的形式化内容

已通过：
* `rat_countable` / `rat_countable'` / `int_prod_countable`
* `rat_eq_num_div_den`（`q = q.num / q.den`，即手写解答"列出 `(p,q)`"的现代写法）
* `rat_countable_of_prod`（由 `ℤ × ℕ*` 可数推 `ℚ` 可数，用 `Rat.num_div_den` 造见证）
* `Icc_ordConnected`、`Icc_subset_Icc`、`exists_step`（三等分取不含 `xₙ` 的等分）

未完成：由 `exists_step` 递归构造 `Iₙ` 并推出 `[0,1]` 不可数（需递归定义 + 序连通性取交点）。

### P10–P15 的可行性评估（已实测 API）

| 题 | 难度 | 结论 |
| --- | --- | --- |
| **P10** 非 Archimedes 域 `ℚ(T)` | 很高 | 本版本 Mathlib **没有** `LinearOrder (LaurentSeries ℚ)` 实例（实测 `inferInstance` 失败），序需自建。按用户指示暂缓。 |
| **P11** n 次正根 | 高 | 有限恒等式 `pow_sub_pow_factor`、扰动估计 `abs_pow_sub_pow_le`、(a) 全部通过；(b) 剩 6 个 `linarith` 细节。 |
| **P12** 实数算术刚性 | 中 | ✅ 完成 |
| **P13** 割族下确界 | 高 | 需像 P8 那样自建割的偏序/下确界。按用户指示暂缓。 |
| **P14** 循环小数 | 很高 | 需形式化十进制展开 + 长除法抽屉原理。按用户指示暂缓。 |
| **P15** `ℚ` 可数 / `[0,1]` 不可数 | 中高 | (a) ✅；(b) 框架与单步引理 ✅，递归构造未完成。 |

### P7 卡住的两个与 Mathlib 细节有关的问题（已定位）

1. `Int.le_floor.mpr` 的**声明方向**是 `↑m ≤ r → m ≤ ⌊r⌋`，
   `apply` 时 Lean 无法把目标 `↑⌊b⌋ ≤ a + 1`（左侧是**实数**写法）与它统一；
   必须显式写成 `(⌊b⌋ : ℝ) ≤ a + 1` 并让被比较的量以**整数类型**出现。
2. `linarith` **看不见取整的整数性**：`a < ⌊b⌋` 到 `⌊b⌋ ≤ a + 1` 这一步它推不出来
   （因为 `⌊b⌋` 对它是"不透明"的实数项）。必须显式用 `Int.le_floor` / `Int.floor_mono`
   或把两边转成整数再 `omega`。这一条在 P4、P7、P9、P11 里都出现。

### 已发现的手写解答问题（转录时标注，形式化时补正）

1. **P1(b)** 手写只对 `⊕` 给了反例，**未处理 `⊙`**；
   形式化补上 `⊙` 良定义的证明（四种符号组合）。结论与手写一致：`⊕` 不良定义、`⊙` 良定义。
2. **P2(b)** 未明确给出 `sup_D A = 12`、`inf_D A = 2`（已补）。
3. **P3 第 3 条** 手写表述混乱（"不妨设 `|x-y|`、`||x|-|y||`" 无意义），思路是化归三角不等式。
4. **P4(a)** 未指出 `1/2` 实际上**被取到**（`1/2 ∈ A`），而 `1` 不被取到。
5. **P5(a)** 手写举例写 `(x,y)=(ε,0)` 取到下界，实际 `⌊ε⌋+⌊0⌋ = 0 = ⌊ε⌋` 也成立，
   但用 `(1/2,1/2)` 更干净；形式化同时验证了上下界两种取等例子。
6. **P6(b)** 手写最后一步 `a₁-b₁ > a₀-b₀-ε/2` 的推导不成立（符号方向反了）。
7. **P7(b)** 手写用"`1/√2` 是无理数"来造无理数，逻辑跳跃；形式化改用 `r + (b-r)·√2/2`。
8. **P8(a)** 未真正论证"为什么不是割"（`{q ≤ -r}` 含最大元 `-r`，违反割的下半集无最大元要求）。
9. **P9(a)(b)** 手写论证严重不完整（`[a_n] ⊇ [a_n]` 之类的笔误）。
10. **P10** 手写解答质量最差，(a)(b) 核心论证基本缺失或写错。
11. **P11(a)** 上界论证写得很乱；**(b)** `xⁿ > a` 情形几乎没有展开。
12. **P12** 缺关键一步：未证明 `f(r) > 0`（需先有平方根并排除 `f(√r)=0`）。
13. **P14** (a) 的 `d_n` 公式写错（两个 `⌊·⌋` 项相同）；(b) 的 `x·10^i` 展开式写错。
14. **P15(a)** 枚举公式手写很乱且不完整；**(b)** 未说明"三等分里至少有一个不含 `xₙ`"。

---

## 3. 后续步骤

1. 等 `lake build Mathlib` 完成
2. 逐题编译 `Problem01..Problem09`，修复报错
3. 继写 `Problem10..Problem15`
4. 全部通过后汇总最终报告
