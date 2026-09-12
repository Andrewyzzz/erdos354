# Erdős 354(i): FE, DB, BG and normalized completeness

已完成有限模板证书、网格基础、合法块表示、初始网格，并将条件永久下降接到
实际地板序列、gcd 模数与到达层事件；进一步证明低缺口完全性、良基下降及
不完全时的最终事件倍率4界，无理比值保证事件无界。现已完成 FE、FE-R、DB、BG
及其累计矛盾，推出归一化完全性，累计审计 358 个定理。
**整篇 #354(i) 与集合强完全性尚未证明。**
实际完成的声明和后续义务见 [STATUS.md](STATUS.md)，环境见
[ENVIRONMENT.md](ENVIRONMENT.md)。

## Reproduce

从包含原始 `certificate/templates.json` 的仓库根目录执行：

```sh
cd formalization
lake exe cache get
python3 scripts/verify.py
python3 scripts/verify.py --fresh
```

已有依赖缓存时可略去 `lake exe cache get`。工具链和全部依赖锁定在
`lean-toolchain`、`lakefile.toml`、`lake-manifest.json` 中，不需要更新版本。
`verify.py` 默认构建根模块 `Dyadic354`，它导入目标定义、证书、循环缺口、网格、
合法表示、初始网格、局部永久下降、实际地板/重排/事件接口、长度估计、
单位网格完全性、有限下降、事件无限性、统一前缀界、FE／DB／BG 全链及公理审计。
脚本再次执行 `Audit.lean`，核对全部本地定理的审计清单，检查实际公理闭包；
缺少输出或出现允许列表以外的公理都会以非零退出码结束。运行开始时会清除旧的
PASS 状态，成功记录附带实际 Lean 源码和依赖锁文件的 SHA-256。

`--fresh` 会创建新的临时源码目录，不复制本项目的编译产物，再执行构建和审计。
它复用锁定的 Mathlib 依赖缓存；不是从零重建 Mathlib，也不是独立编译器验证。
临时目录保留，路径记录在日志中，便于出现问题时检查。

## Mathematical scope

`Certificate.certificate_correct` 对所有布尔首、次位型（首位型非零）及所有
整数 `p,q` 满足 `0 < q < p < 2*q` 给出一条正确链。它包括：

- 六个位置的有限掩码支持，每个位置至多使用一次；掩码求值等于实际六项的子集和。
- 两个备选偏移的常数为 `c` 和 `c+1`，对任意第三位型均有 `0 ≤ c`、`c+1 ≤ 22`。
- 由掩码重算系数，并核对节点端点确实为 `max` 与 `min + p + q`。
- 严格节点宽度、双向严格相邻交叠、首尾覆盖，以及 `[p+2*q, 7*p+6*q]` 的整数区间覆盖。
- 全部 12 个模板均正确，共 125 个节点、113 个相邻连接；每个节点量化全部 4 个第三位型。

锥域结论通过通用代数引理证明，不枚举 `p,q`。实际数据用 `decide +kernel`
核验；生成脚本只转换数据，不被当作数学正确性的信任来源。JSON 中的 `lo/hi`
作为待检验的候选端点读入，其正确性必须通过 Lean 对掩码重算的检查。

这里的六项是主稿 §3 给出的代数表达式。第三批已经证明它们与旧前缀、精确倍增块
的合法不交拼接，并从实际12条模板构造初始有限子集和网格。
原索引映射及其单射性已证明；第四批已从实数地板递推导出实际块及六项恒等式。

第二批新增的 `CyclicGaps.erosion_exact`、`Mesh.translate_union_gap_span` 和
`Mesh.projection_gap` 分别对应主稿 Lemma 2.1、2.2、2.3。
`Mesh.propagate_iterate` 对满足 `0 < c_n`、`c_{n+1} ≤ 2*c_n` 的任意后续权重，
证明每一步仍保持同一网格缺口界，并给出精确跨度增量。

循环缺口是每个长度 `h+1` 窗口均被命中的最小 h；
`missingRun_iff_le_gap` 证明这恰好是实际连续缺失段的最大长度。有限整数网格的
gap 直接定义为所有实际相邻点距离的最大值，`meshOn_iff_gap_le` 再证明与窗口
命中表述的等价。所有模缺口定理都要求正模数，覆盖模数 1；空集和单点整数网格
的 gap 约定为 0，单点 span 为 0。循环缺口仅对非空剩余集定义，满集缺口为 0。

第三批 `InitialMesh.prefix_initial_mesh` 在明确的块恒等式、非负旧权重及总和界下，
构造原前缀内的网格，证明 gap ≤ max(1,旧缺口)，span > `8dKq+15`。
`PermanentMesh.certificate_permanent_descent` 再从该构造推出全部后续合适模数上的
前缀缺口 ≤ 旧缺口−1（自然数截断减法），没有把网格存在或下降本身作为前提。

第三批通用局部定理要求未来项为正、相邻项至多翻倍、首项上界和模数上界。
第四批从实际地板递推推导这些条件；`PairReindex.prefixSums_reindex` 证明未来
`b,a` 枚举与冻结的 `a,b` 枚举在每个完整成对前缀上有完全相同的合法子集和值。
`FloorDescent.long_block_descent` 将局部下降实例化为实际 `D_t=gcd(a_t,b_t)` 上的缺口界。

`BlockLength.next_event_length_descent` 的含义是：若
`0<b_0<a_0<2b_0`，`n<m`，到达层区间 `(n,m)` 无事件、m 是事件，且
`m−n≥2n+C`，则对每个 `t≥m+3` 有 `h_t≤max(0,h_n−1)`。
这里明确取仅依赖 M=a_0 的宽松常数 `C=(16(M+1)²).toNat`；没有要求 C 是最优常数。
节点、实际表示、未来重排、gcd 约化和长度估计均在证明链内。

第五批 `UnitMesh.unit_mesh_half_line` 从实际单位网格构造全部充分大整数的合法
有限索引表示，`LowGap.next_event_length_complete` 因此证明合格长块及旧缺口≤1
推出冻结交错列的完全性。没有把网格无界或索引表示合法性当作新假设。

`EventGaps.unbounded_qualifying_complete` 用自然数良基下降证明，无界合格起点
推出完全性；每次选点都在前次永久更新生效之后，不需要普通转换的缺口单调性。
它不借用未证明的统一前缀缺口界，也不声称已证明原稿 N−1 次更新预算。
反过来，不完全的归一化序列最终没有合格间隔，故相邻事件满足 `m<3n+C` 和 `m≤4n`。

`EventInfinitude.events_unbounded` 从无理比值证明真实事件无界；`nextEvent` 定义
最小后继，相关定理保证它实际存在且中间没有其他事件。
当前组合结论 `incomplete_nextEvent_factor_four` 的明确前提是无理比值、
归一化地板初值和不完全性，结论是实际后继事件最终满足倍率4界。

第六批 `PrefixMesh.prefix_gap_bound` 证明首项控制全部前缀 gap，包含平移凸包
分离时的新桥接缺口。`PrefixBounds.uniform_cyclic_gap` 实例化到实际地板列，
给出 `n≥2` 时 `h_n≤N−1`；内部缺失段≤N−1 的界对每个 n 成立。
跨度条件 `S_n≥a_n` 由第2层起的直接归纳证明，不借用未形式化的指数下界。

`FECounting.values_step` 与 `deficit_step` 证明主稿 (8.1)。Q、G 使用整数差定义，
非负性由不交基本复制及真实窗口范围证明；`deficit_eq_holes` 和 `growth_eq_newValues`
进一步识别实际缺失/新增整数值的个数，所有 Finset 都按不同和值计数，不计掩码重数。
同时已证明 `B_n=M+N+Σw_i`、`0<B_n<3N+2n` 及数字和与到达事件的等价。

第七批完成 FE 的周期边界、变周期比较、非重叠衰减与误差预算，得到原稿常数的
`FE.deficit_exponential_bound` 和真实连续种子界 `FER.seed_exponential_bound`。
`DB.digit_propagation` 从有限系数的合法表示给出数字预算增量；
`DBScale.advance_increment` 把它接到已定义并证明存在的首个好分母 crossing。

长窗口、层高及精度由 Dirichlet 逼近和 crossing 最小性实际构造。
返回成本用稀疏二进制比值的全有理紧集证明，对任意共同乘数有效。
`BG.bounded_event_windows_complete` 完成累计矛盾，
`BG.normalized_complete` 进一步用已证明的倍率4后继事件界消去事件窗口前提。
归一化主定理的全部数学前提仅为
`0 < ⌊β⌋ < ⌊α⌋ < 2⌊β⌋` 和 `Irrational (α/β)`；没有假设 FE、DB、BG 或长平台存在。

本实现采用经过证明的替代接口，不逐字复现连分数枚举、显式最小 popcount 或原稿
每个渐近中间常数，具体对应见 `STATUS.md` 第七批部分。
**仍需完成一般正参数的合法归一化、取尾与集合去重/有限删除，以及上游原题对接。
归一化完全性不等于任意正参数的 `PartI`，更不等于集合强完全性。**

## Source map

| File | Purpose |
|---|---|
| `Dyadic354/Statements.lean` | 原题与强完全性的固定定义；显式阈值等价式 |
| `Dyadic354/Basic.lean` | 有限子集和值与整数锥引理 |
| `Dyadic354/Certificate.lean` | 通用检查器、掩码语义、区间链及正确性证明 |
| `Dyadic354/CertificateData.lean` | 原始 JSON 的可重生成数据与实际证书定理 |
| `Dyadic354/CyclicGaps.lean` | 最长循环缺失段、精确侵蚀、满集及模数1边界 |
| `Dyadic354/Mesh.lean` | 实际相邻点距离、窗口等价、平移传播、模投影与逐步归纳 |
| `Dyadic354/CoefficientInterval.lean` | Bézout 有界系数区间、反射与二进制有限支持 |
| `Dyadic354/Representations.lean` | 不交表示、倍增块与原索引单射 |
| `Dyadic354/NodeRepresentations.lean` | 实际旧代表、余量界、节点表示及窗口命中 |
| `Dyadic354/InitialMesh.lean` | 缩短窗口链、常数预算、实际有限子集和初始网格 |
| `Dyadic354/PermanentMesh.lean` | 原前缀追加合法性、任意后续模数投影与局部下降 |
| `Dyadic354/FloorSequence.lean` | 真实地板误差、二进制递推、初值分离保持与前缀总和界 |
| `Dyadic354/PairReindex.lean` | 未来成对交换、单射、完整成对前缀子集和不变与实际未来权重界 |
| `Dyadic354/ExactBlock.lean` | 到达层事件、零位与倍增块、实际六项及下一小权重界 |
| `Dyadic354/FloorDescent.lean` | 实际 gcd 坐标、实际前缀模集以及地板序列条件永久下降 |
| `Dyadic354/BlockLength.lean` | 多项式门槛、地板增长界和仅依赖初值的块长充分条件 |
| `Dyadic354/UnitMesh.lean` | 实际单位网格的合法扩展、右端点无界和半直线覆盖 |
| `Dyadic354/LowGap.lean` | 合格长块与低缺口推出冻结交错列完全性 |
| `Dyadic354/EventGaps.lean` | 延迟永久下降的良基论证、不完全时的相邻事件界 |
| `Dyadic354/EventInfinitude.lean` | 无理性保证事件无界、真实最小后继及最终倍率4界 |
| `Dyadic354/PrefixMesh.lean` | 凸包分离时的桥接界、原前缀递推、统一 gap 与内部缺失段界 |
| `Dyadic354/PrefixBounds.lean` | 实际前缀总和、跨度及 (1.1) 的统一 gcd 模缺口界 |
| `Dyadic354/FECounting.lean` | 真实不同和值的四平移递推、B/Q/G、非负性及实际缺失/新增计数 |
| `Dyadic354/CyclicBoundary.lean`、`PeriodicWord.lean`、`FEShift.lean` | 周期缺失函数、变差与移位新增和值 |
| `Dyadic354/FEMissingRuns.lean`、`IntervalSums.lean`、`PeriodChange.lean`、`EventBoundary.lean` | 缺失段边界计数、区间求和、变周期比较与非零事件边界 |
| `Dyadic354/FERecurrence.lean`、`EventDecay.lean`、`FE.lean` | 非重叠事件块、势函数误差控制及 FE |
| `Dyadic354/ContiguousSeed.lean`、`FER.lean` | 实际最长连续区间与 FE-R |
| `Dyadic354/DBDigits.lean`、`DBPhases.lean`、`DBWindows.lean` | 实际数字预算、Bézout 相位与合法有限系数窗口 |
| `Dyadic354/DBCover.lean`、`DB.lean` | 连续覆盖、索引合法拼接与 DB 增量 |
| `Dyadic354/RationalWindows.lean`、`CubicGrowth.lean`、`DBScale.lean` | 好有理数 crossing、立方深度矛盾与实际 DB 尺度 |
| `Dyadic354/BGSparseCompact.lean`、`BGBinaryRatio.lean`、`BGReturns.lean` | 有理紧集、二进制支持、统一返回成本发散 |
| `Dyadic354/BGExactLayers.lean`、`BGWindowBounds.lean`、`BGWindows.lean` | 非精确层计数、逼近精度和实际任意长稀疏窗口 |
| `Dyadic354/BGGeometric.lean`、`BGCapacity.lean`、`BG.lean` | 不重叠返回累计、窗口容量、BG 及归一化完全性 |
| `Dyadic354/Audit.lean` | 目标类型输出与全部已完成定理的公理审计 |
| `scripts/generate_data.py` | 数据翻译及与 JSON 的一致性检查 |
| `scripts/verify.py` | 构建、公理允许列表、独立目录重建 |

上游定义来源与许可见 [UPSTREAM.md](UPSTREAM.md)。公开稿件及原始证书保持原样。
