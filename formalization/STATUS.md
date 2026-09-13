# 第八批状态：原题与强完全性

**冻结的 #354(i) 与稿件的集合强完全性目标均已证明：参数为任意正实数，
仅要求比值无理，不再要求归一化初值，也没有额外 FE／DB／BG 假设。**

最终主结论为：

```lean
Dyadic354.erdos354_part_i : Dyadic354.PartI
Dyadic354.erdos354_strong_completeness : Dyadic354.StrongCompleteness
```

第一个结论使用有限自然数索引集选择求和项；第二个结论删除任意有限个数值，
用剩余数值的有限集合表示充分大的整数。同一索引或数值均不会非法重复使用。
上游正面命题的精确定义适配也已完成，见 `UpstreamBridge.erdos354_part_i_upstream`。
这是本地 Lean 内核验证结果，不等于社区接受、期刊发表、外部 checker 复核或
完整上游工程构建；工具链及定义适配边界见 `UPSTREAM.md`。

实际证书由 Lean 内核计算核验，通过通用 soundness 定理得到全部合法整数参数上的
系数覆盖与六项子集和语义。第二批证明主稿 Lemma 2.1、2.2、2.3，并补齐最长缺失段、
实际相邻点距离与窗口表述之间的连接。第三批增加主稿 §3–4 的有限表示链及 §5 的局部
代数投影链，共增加 32 个定理。第四批增加 44 个定理，完成地板递推、成对重排、
实际局部块、gcd 坐标、条件永久下降及长度估计。第五批增加 21 个定理，补齐低缺口
完全性、良基下降、无理比值下的事件无限性及真实后继事件倍率界。
第六批增加 35 个定理，完成 §1.1 的统一前缀/内部/模缺口界，以及 §8 的有限计数基础。
第七批增加 175 个定理，将 FE／DB／BG 连接为实际归一化完全性结论。
第八批增加 23 个定理，完成合法取尾、去重、有限删除与最终目标适配。
有限数据使用 `decide +kernel`，累计 381 个本地定理的
传递公理依赖均为 `propext`、`Classical.choice`、`Quot.sound` 的子集。
最终构建与审计见 `logs/verification.json`，独立目录重建见
`logs/fresh-verification.json`；完整实际输出保存在同目录的日志。

以下第一至第七批保留各阶段当时的接口与完成边界；其中“尚未完成”是历史状态，
当前状态以第八批及文末验收边界为准。

## 第一批已编译定理与主稿对应（20个）

下表中的名称均为完整声明名；每行已实际编译，且列入 `Audit.lean`。

| 完整声明名 | 对应内容 | 主要依赖 |
|---|---|---|
| `Dyadic354.mem_finiteSubsetSums` | §1：不同有限子集和值 | Finset powerset/image |
| `Dyadic354.Linear.eval_add` | §3.3：系数加法语义 | 整数环运算 |
| `Dyadic354.Linear.eval_sub` | §3.3：系数差语义 | 整数环运算 |
| `Dyadic354.Linear.cone_identity` | §3.3：整数锥换元恒等式 | 整数环运算 |
| `Dyadic354.Linear.nonneg_on_cone` | §3.3：闭锥非负性 | cone_identity、乘法保序 |
| `Dyadic354.Linear.positive_on_cone` | §3.3：开锥严格正性 | cone_identity、严格乘法保序 |
| `Dyadic354.indexedComplete_iff` | 原题：充分大的整数阈值 | Filter.eventually_atTop |
| `Dyadic354.Certificate.offset_eq_sum` | §3.2：掩码求值等于六项子集和 | 有限和分配律 |
| `Dyadic354.Certificate.offset_isSubsetSum` | §3.2：有限原始位置支持 | offset_eq_sum |
| `Dyadic354.Certificate.weights_explicit` | §3：六个实际代数权重 | Fin 6 分情况、整数环运算 |
| `Dyadic354.Certificate.endpoints_sound` | §3.2–3.3：max/min 端点 | nonneg_on_cone、掩码系数 |
| `Dyadic354.Certificate.node_sound` | §3.2–3.3：节点宽度、常数差与合法备选表示 | endpoints_sound、positive_on_cone、offset_isSubsetSum |
| `Dyadic354.Certificate.interval_chain_covers` | §3.3：区间链覆盖，不要求端点单调 | 自然数归纳、整数序 |
| `Dyadic354.Certificate.chain_sound` | §3.3：节点、双向交叠、端点与全区间覆盖 | node_sound、interval_chain_covers |
| `Dyadic354.Certificate.checkCertificate_sound` | §3.3：检查通过蕴含通用数学结论 | chain_sound、布尔检查语义 |
| `Dyadic354.Certificate.certificate_checked` | 附录A：当前12类输入检查通过 | 原始掩码数据、decide +kernel |
| `Dyadic354.Certificate.certificate_correct` | §3.3与附录A：全部合法参数的完整证书结论 | checkCertificate_sound、certificate_checked |
| `Dyadic354.Certificate.all_templates_checked` | 附录A：列表中的每个模板均通过 | 原始掩码数据、decide +kernel |
| `Dyadic354.Certificate.all_templates_correct` | 附录A：每个实际模板的通用数学含义 | all_templates_checked、chain_sound |
| `Dyadic354.Certificate.certificate_counts` | 附录A：12模板、125节点、113连接 | 原始数据、decide +kernel |

每个节点的常数结论量化全部 4 个第三位型，共覆盖 500 个节点/第三位型组合。
这里的通用参数是主稿使用的整数 `p,q`；它们没有被限制到有限测试范围。

## 第二批已编译定理与主稿对应（31个）

下表所有声明均已编译并列入公理审计。`CyclicGaps.gap` 的值是自然数，因此
`h-1` 使用截断减法，正好表达 `max(0,h-1)`。

| 完整声明名 | 对应内容 | 主要依赖 |
|---|---|---|
| `Dyadic354.CyclicGaps.gapBound_mono` | 窗口长度放宽 | 窗口定义 |
| `Dyadic354.CyclicGaps.not_missingRun_iff` | 缺失段与窗口命中互补 | 量词对偶 |
| `Dyadic354.CyclicGaps.gapBound_erode_iff` | Lemma 2.1：侵蚀与窗口长度的精确关系 | 整数窗口平移 |
| `Dyadic354.CyclicGaps.modulus_bound` | 非空模集的缺口小于模数 | ZMod代表元及其界 |
| `Dyadic354.CyclicGaps.gap_spec` | 最小窗口界确实成立 | Nat.find_spec、modulus_bound |
| `Dyadic354.CyclicGaps.gap_le_iff` | 数值缺口界与窗口命中等价 | Nat.find最小性、gapBound_mono |
| `Dyadic354.CyclicGaps.gap_lt_modulus` | 排除全空循环，保证有限缺口 | modulus_bound、gap_le_iff |
| `Dyadic354.CyclicGaps.missingRun_iff_le_gap` | 缺口值就是最长实际连续缺失段 | gap_le_iff、not_missingRun_iff |
| `Dyadic354.CyclicGaps.erode_nonempty` | 侵蚀后仍非空 | Finset并集 |
| `Dyadic354.CyclicGaps.lift_erode` | 模集侵蚀与整数周期提升一致 | ZMod加减法、Finset像 |
| `Dyadic354.CyclicGaps.erosion_exact` | **Lemma 2.1：h(X∪(X+1))=h(X)-1** | gapBound_erode_iff、gap最小性 |
| `Dyadic354.CyclicGaps.gap_eq_zero_iff_full` | 缺口为0当且仅当满集 | ZMod代表元、gap_spec |
| `Dyadic354.CyclicGaps.gap_modulus_one` | 模数1的边界情形 | gap_lt_modulus |
| `Dyadic354.Mesh.gap_le_iff` | 实际相邻点最大距离的界 | Finset.sup |
| `Dyadic354.Mesh.gap_empty` | 空整数集的gap为0 | 空有限上确界 |
| `Dyadic354.Mesh.gap_singleton` | 单点整数集的gap为0 | 不存在相邻点 |
| `Dyadic354.Mesh.encloses_min_max` | 凸包端点与所有元素的界 | Finset.min'/max' |
| `Dyadic354.Mesh.span_of_encloses` | 实际跨度等于两端点之差 | 最小值与最大值 |
| `Dyadic354.Mesh.span_singleton` | 单点跨度为0 | Finset.min'/max' |
| `Dyadic354.Mesh.meshOn_gap_le` | 窗口命中蕴含真实相邻间距界 | Consecutive、窗口命中 |
| `Dyadic354.Mesh.meshOn_of_gap_le` | 真实相邻间距界蕴含窗口命中 | 有限集合的前驱与后继 |
| `Dyadic354.Mesh.meshOn_iff_gap_le` | 网格窗口表述与原稿gap表述等价 | 上述两个方向；k>0 |
| `Dyadic354.Mesh.gap_positive_of_encloses` | 正跨度强制正gap | 凸包首点的后继 |
| `Dyadic354.Mesh.meshOn_translate_union` | 凸包相交或接触时平移保持窗口界 | 原凸包/平移凸包分情况 |
| `Dyadic354.Mesh.translate_union_nonempty` | 平移并集非空 | Finset并集 |
| `Dyadic354.Mesh.translate_union_gap_span` | **Lemma 2.2：gap不增，span精确增加c** | 窗口等价、平移凸包、端点唯一性 |
| `Dyadic354.Mesh.residues_nonempty` | 非空网格模像非空 | Finset.image |
| `Dyadic354.Mesh.projection_window_bound` | 任意模窗口都由整数网格命中 | ZMod代表元、网格窗口；包括循环边界 |
| `Dyadic354.Mesh.projection_gap` | **Lemma 2.3：span≥m>0时h(W mod m)≤k-1** | projection_window_bound、gap_le_iff |
| `Dyadic354.Mesh.extend_nonempty` | 每步加入未来权重后的集合非空 | 递归并集 |
| `Dyadic354.Mesh.propagate_iterate` | Lemma 2.2后推论：每一步gap界保持、精确累计跨度 | translate_union_gap_span、自然数归纳 |

模缺口仅对非空 `Finset (ZMod d)` 且 `NeZero d` 定义。证明覆盖满集、零长度缺失段、
模数1；整数网格的空集和单点gap为0，单点span为0。平移主定理直接使用原稿条件
`span(W) ≥ c > 0`；所需 `k>0` 从这些条件推导，并未作为额外前提附加。
投影定理同样从 `span(W) ≥ m > 0` 推导正gap；没有把不同模数视作同一个群。

## 第三批已编译定理与主稿对应（32个）

以下名称均以 `Dyadic354.` 开头；所有辅助定理也纳入审计，没有只审计末端结论。
准确参数与类型见 `logs/axioms.log` 和相应 Lean 源码。

| 声明名（省略共同前缀） | 对应内容 |
|---|---|
| `CoefficientInterval.lower_interval` | §3.1：Bézout 系数取模，构造有界 x、y |
| `CoefficientInterval.bounded_interval` | §3.1：反射得到全部 `[F,(p+q)(K-1)-F]` |
| `CoefficientInterval.binary_sum_exists` | 小于 `2^ℓ` 的自然数由不同二进制位置求和 |
| `Representations.subsetSum_disjSum` | 不交索引类型上的合法子集和拼接 |
| `Representations.subsetSum_embed` | 单射映射到指定索引集，保留不重复性 |
| `Representations.binary_scaled` | 整数倍二进制系数由 `Fin ℓ` 位置实现 |
| `Representations.block_interval` | §3.1：两条倍增块真正实现旧系数区间 |
| `Representations.position_injective` | 旧前缀、两条倍增块、六项的原索引两两不交 |
| `Representations.position_lt` | 全部原索引严格小于 `2(n+ℓ+3)` |
| `Representations.packed_weights_match` | 显式两条倍增恒等式及六项恒等式对应局部模型 |
| `Representations.packed_to_prefix` | 局部表示转为原始前缀有限索引和 |
| `Representations.prefix_block_offset` | §3.2：旧前缀 + 倍增块 + 六项偏移的合法拼接 |
| `NodeRepresentations.residual_bounds` | §3.2：实际旧代表与常数22下的剩余系数上下界 |
| `NodeRepresentations.old_sum_bounds` | 非负旧权重的每个子集和在 `[0,Σold]` 内 |
| `NodeRepresentations.mask_representation` | §3.2：单掩码在缩短节点区间内实现对应余数 |
| `NodeRepresentations.node_representation` | §3.2：每个已核验节点实现两类旧余数 |
| `NodeRepresentations.oldResidues_nonempty` | 旧前缀模集包含空和余数 |
| `NodeRepresentations.lift_oldResidues_iff` | 模集成员等价于实际旧代表与整除条件 |
| `NodeRepresentations.node_window` | §3.2：侵蚀后每个节点内 k 窗口命中实际子集和 |
| `InitialMesh.margin_budget` | (4.1)：`dK-2B ≥ 64d-42 ≥ 22d`，包括 d=1 |
| `InitialMesh.trimmed_chain_covers` | §4：缩短窗口链覆盖，不假设端点单调 |
| `InitialMesh.chain_windows` | §4：全局区间内每个 k 窗口命中实际子集和 |
| `InitialMesh.mesh_from_windows` | (4.2)：实际有限网格、两端损失及跨度界 |
| `InitialMesh.span_budget` | (4.3)：跨度下界严格大于 `8dKq+15` |
| `InitialMesh.certificate_initial_mesh` | 从原始12条模板及局部块条件构造实际子集和网格 |
| `InitialMesh.prefix_initial_mesh` | 初始网格每个点均为原前缀合法有限索引和 |
| `PermanentMesh.prefix_nonempty` | 每个原前缀含空和 |
| `PermanentMesh.extend_step_subset` | 追加一个新索引不与旧支持冲突 |
| `PermanentMesh.extend_subset_prefix` | 每一步传播网格仍包含于实际前缀子集和 |
| `PermanentMesh.gap_of_subset` | 非空模集增大时循环缺口不增 |
| `PermanentMesh.permanent_projection` | 给定合法初始网格及未来权重界，任意后续较小模数上的前缀缺口界 |
| `PermanentMesh.certificate_permanent_descent` | 从实际模板出发，在显式局部块及未来权重条件下，所有后续合适模数的缺口不超过旧缺口减1 |

### 第三批定理的局部接口

`certificate_initial_mesh` 的条件为正整数模数 d，整数 `0<q<p<2q`，
`IsCoprime p q`，非负旧权重且旧总和 `<d(p+q)`，`K=2^ℓ≥K_*`，非零首位型。
`IsCoprime` 是 Mathlib 标准的整数 Bézout 定义。系数并未限制在有限枚举范围内。
网格由这些权重的有限子集和值构造，既不是抽象余数网格，也没有把网格存在作为假设。

`prefix_initial_mesh` 进一步把位置显式映射为旧前缀 `[0,2n)`、
倍增块的 `2n+2i` / `2n+2i+1`、六项的 `2n+2ℓ+j`。
该映射已证明是单射；与给定序列 v 的对应由两条块恒等式和六项恒等式明确表达。
第三批没有从实数地板函数、事件与 gcd 推导这些局部假设；第四批已经补上该接口，见下节。

`certificate_permanent_descent` 没有假设网格存在或缺口下降；二者在定理内部证明。
但仍显式要求未来权重为正、后一项不超过前一项两倍、第一未来项
`≤8dKq+15`，以及所选新模数不超过当前未来项。它量化所有这样的未来延拓与模数。
**这只是 §5 的局部代数版本，不能声称 §2–6 已全部形式化。**

特别注意未来项的顺序：主稿传播使用 `b_r,a_r,b_{r+1},a_{r+1},…`；
冻结的原题定义是 `a_r,b_r,a_{r+1},b_{r+1},…`。第四批通过显式的索引对换、
完整成对前缀和值不变及地板递推证明解决这一接口，没有修改冻结的原题定义。

## 第四批已编译定理与主稿对应（44个）

以下名称均省略共同前缀 `Dyadic354.`；每个辅助定理都列入公理审计。

| 声明名 | 对应内容 |
|---|---|
| `FloorSequence.correction_bounds` | §1：真实地板误差在整数区间 `[0,1]` |
| `FloorSequence.digit_bit` | 布尔位求值等于真实误差 |
| `FloorSequence.recurrence` | `a_(n+1)=2a_n+u_n`，不是额外假设 |
| `FloorSequence.next_bounds` | 单列下一项介于两倍与两倍加1之间 |
| `FloorSequence.normalized_bounds` | 归一化初值的 `0<b_n<a_n<2b_n` 对所有层保持 |
| `FloorSequence.prefix_deficit` | 单列当前项减旧前缀和的精确恒等式 |
| `FloorSequence.prefix_sum_lt` | 正初值下单列旧前缀和严格小于当前项 |
| `FloorSequence.interleave_even` | 冻结交错定义在偶数位置取第一列 |
| `FloorSequence.interleave_odd` | 冻结交错定义在奇数位置取第二列 |
| `FloorSequence.paired_prefix_sum` | 完整成对前缀和等于两列前缀和 |
| `FloorSequence.paired_prefix_lt` | §1、§3：实际 `S_n<a_n+b_n` |
| `PairReindex.swapAfter_before` | 更新层之前的每个原索引保持不变 |
| `PairReindex.swapAfter_even` | 更新层之后交换偶数位置 |
| `PairReindex.swapAfter_odd` | 更新层之后交换奇数位置 |
| `PairReindex.index_cases` | 自然数索引的二分解 |
| `PairReindex.swapAfter_involutive` | 成对交换两次是恒等映射 |
| `PairReindex.swapAfter_injective` | 不会碰撞或重复使用原索引 |
| `PairReindex.swapAfter_lt_iff` | 每个完整成对前缀的索引范围保持不变 |
| `PairReindex.prefixSums_reindex_subset` | 重排前后合法子集和值的一个包含方向 |
| `PairReindex.prefixSums_reindex` | 重排前后每个完整成对前缀的全部子集和值相等 |
| `PairReindex.sortedTail_even` | 新未来枚举的偶数位置实际为 b 项 |
| `PairReindex.sortedTail_odd` | 新未来枚举的奇数位置实际为 a 项 |
| `PairReindex.sortedTail_positive` | 从归一化地板初值得到未来每项严格为正 |
| `PairReindex.sortedTail_doubling` | 从地板递推得到未来相邻项至多翻倍 |
| `ExactBlock.no_events_zero_digits` | 到达层区间无事件蕴含对应离开位全为零 |
| `ExactBlock.exact_block` | ℓ−1 次零转换给出 ℓ 个精确倍增权重 |
| `ExactBlock.after_exact_block` | 第 ℓ 次转换位于到达层 n+ℓ，明确偏移一位 |
| `ExactBlock.interleave_block` | 冻结交错列上的两条实际倍增块恒等式 |
| `ExactBlock.three_pairs` | 实际连续三对权重等于证书六项向量 |
| `ExactBlock.six_after_exact_block` | 从零转换块自动推出证书六项输入 |
| `ExactBlock.next_small_weight_bound` | 从真实误差界推出 `b_(n+ℓ+3)≤8dKq+15` |
| `FloorDescent.fin_prefix_iff` | `Fin(2n)` 与自然数前缀的合法表示等价 |
| `FloorDescent.oldResidues_prefix` | 证书旧余数集等于实际交错列前缀的模像 |
| `FloorDescent.modulus_positive` | 正 b 项保证当前实际 gcd 为正 |
| `FloorDescent.gcd_coordinates` | 除实际 gcd 得到 `a=dp,b=dq,0<q<p<2q` 及 Bézout 互素性 |
| `FloorDescent.interleave_positive` | 归一化后冻结交错列每个原始权重都为正 |
| `FloorDescent.long_block_descent` | §5：实际地板列长零块与末端事件触发永久下降 |
| `FloorDescent.next_event_descent` | 到达层版本：末端事件在 m，更新从 m+3 生效 |
| `BlockLength.threshold_le_square` | §5：`K_*≤16p²` |
| `BlockLength.floor_upper` | `a_n<(M+1)2^n` |
| `BlockLength.coordinate_upper` | 实际约化坐标 `0<p≤a_n<(M+1)2^n` |
| `BlockLength.growthConstant_bound` | 仅依赖初始 M 的显式常数控制 `16(M+1)²` |
| `BlockLength.threshold_of_length` | 块长 `ℓ≥2n+C` 蕴含证书要求 `2^ℓ≥K_*` |
| `BlockLength.next_event_length_descent` | 实际无事件区间的长度条件蕴含从 m+3 起永久下降 |

### 第四批末端结论及其前提

`BlockLength.next_event_length_descent` 针对实际
`a_i=⌊2^i α⌋, b_i=⌊2^i β⌋`，在以下条件下成立：

1. 初值满足 `0<b_0<a_0<2b_0`（一般正实数参数如何合法归一化仍待证明）。
2. `n<m`，到达层开区间 `(n,m)` 内无事件，m 是事件。
3. `m−n≥2n+C`，其中本工程明确取 `C=(16(a_0+1)²).toNat`。

结论是：**对每个 `t≥m+3`，实际 gcd 模数上的实际前缀缺口满足
`h_t≤h_n−1`（自然数截断减法）**。
这里 `D_t=gcd(a_t,b_t)`，不是任意输入的替代模数；前缀由冻结交错列的有限自然数
索引集取和。旧总和界、互素性、六项输入、未来正性、两倍界和首项界均在证明中导出，
不再作为该末端定理的独立前提。依赖链实际包含原始12条模板的内核核验证书。

常数 C 故意取得宽松，未追求对数级最优值；它只依赖初始第一列的地板 M，
不依赖未来位串、事件或模数。该条件性结论无需无理性，不能据此声称已证明原题。
第四批结束时，低缺口完全性、无限事件与有限下降仍未完成；第五批的补充如下。
FE/DB/BG 仍未完成。

## 第五批已编译定理与主稿对应（21个）

以下名称均省略共同前缀 `Dyadic354.`；全部列入公理闭包审计。

| 声明名 | 对应内容 |
|---|---|
| `PairReindex.isSubsetSum_reindex_iff` | 未来成对交换保持全部合法有限索引和值 |
| `PairReindex.indexedComplete_reindex_iff` | 重排前后的索引完全性等价 |
| `FloorDescent.long_block_mesh` | 提取实际长块产生的网格，供下降和完全性共同使用 |
| `UnitMesh.mem_extend` | 原网格点在所有未来扩展中保留 |
| `UnitMesh.add_sum_mem_extend` | 选取全部新索引，给出合法的右端点增长下界 |
| `UnitMesh.positive_sum_ge_length` | 正整数未来权重的前缀和至少等于项数 |
| `UnitMesh.unit_mesh_half_line` | §5：实际单位网格及合法延拓覆盖从固定左端点起的半直线 |
| `UnitMesh.unit_mesh_complete` | 半直线覆盖转为冻结的 `IndexedComplete` 定义 |
| `LowGap.long_block_complete` | §5：实际长块、证书门槛及旧缺口 ≤1 推出原交错列完全性 |
| `LowGap.next_event_length_complete` | 同一结论的到达层与显式块长版本 |
| `EventGaps.eventually_not_of_eventual_descent` | §6：允许延迟生效的永久严格下降，排除无界合格起点 |
| `EventGaps.incomplete_eventually_no_qualifying` | 不完全的归一化序列最终没有合格长间隔 |
| `EventGaps.unbounded_qualifying_complete` | 无界合格长间隔推出实际索引完全性 |
| `EventGaps.incomplete_event_step_bound` | 不完全时实际相邻事件最终满足 `m<3n+C` |
| `EventGaps.incomplete_event_factor_four` | §6：进一步得到实际相邻事件最终满足 `m≤4n` |
| `EventInfinitude.zero_tail_dyadic` | 地板误差最终全零迫使参数为二进有理数 |
| `EventInfinitude.no_events_tail_digits` | 到达层尾部无事件等价方向：对应两列位均为零 |
| `EventInfinitude.events_unbounded` | §1：无理比值保证每个层数之后都有实际事件 |
| `EventInfinitude.nextEvent_spec` | 最小后继是真实事件，且严格晚于给定层 |
| `EventInfinitude.no_event_before_next` | 给定层与最小后继之间确实没有事件 |
| `EventInfinitude.incomplete_nextEvent_factor_four` | 对由无理性保证存在的真实后继，最终有 `nextEvent(n)≤4n` |

### 第五批结论、前提和证明边界

1. **单位网格真正推出完全性。** `unit_mesh_half_line` 从原前缀中的有限网格出发，
   要求 gap≤1、跨度足以接入第一项、未来正整数权重相邻至多翻倍。
   它构造合法延拓，证明右端点无界；没有把无界网格或半直线存在当作假设。
   `LowGap.next_event_length_complete` 从实际地板列推导这些条件，并通过已证明的
   重排等价回到冻结的原始交错定义。**单独缺口≤1并非本定理的充分前提**；还需要
   合格块及归一化初值。
2. **有限下降无需逐次转换单调性。** `eventually_not_of_eventual_descent` 以缺口值
   作自然数强归纳，每次在永久更新生效之后选取更晚的合格起点。
   本批因此不需要先借用尚未证明的统一 `h_n≤N−1` 界，也没有声称已形式化主稿
   “至多 N−1 次更新”的数值预算。这是实现 §6 定性结论的另一条良基证明。
3. **无理性保证实际事件存在。** 若两列尾部位均为零，利用地板不等式及二的幂无界，
   证明 `α=a_N/2^N`、`β=b_N/2^N`，于是比值有理，矛盾。
   `events_unbounded` 不需要归一化或正参数前提。`nextEvent` 是实际事件集合的最小
   后继，存在性、严格晚于起点及中间无事件均有已编译证明。
4. **当前组合结论。** 假设 `Irrational (α/β)`、`0<b_0<a_0<2b_0` 和交错列不完全，
   则存在 N，使每个 `n≥N` 的真实后继事件满足 `nextEvent(n)≤4n`。
   其中没有 FE、DB、BG、下降或事件存在的占位假设；但“不完全”在这里是明确的
   反证前提，**尚未推出矛盾**。更精确的 `m<3n+C` 也已证明，实数比值的
   `limsup≤3` 陈述本批没有另外形式化。

因此第3里程碑的定性永久下降—事件倍率结论已经接通；仍不称 §2–6 每一项陈述
均已逐字形式化。后续的 FE/DB/BG 累计矛盾仍是主要未完成部分。

## 第六批已编译定理与主稿对应（35个）

以下名称均省略共同前缀 `Dyadic354.`；全部辅助定理纳入审计。

| 声明名 | 对应内容 |
|---|---|
| `PrefixMesh.translate_union_mesh` | §1.1：平移凸包可分离，显式支付两凸包之间的新缺口 |
| `PrefixMesh.prefix_zero` | 空前缀的不同和值集合恰为 `{0}` |
| `PrefixMesh.prefix_step` | 追加一个原索引的精确子集和集合等式，不只是包含关系 |
| `PrefixMesh.prefix_encloses` | 非负权重前缀的实际两端点为 0 与总和 |
| `PrefixMesh.prefix_span` | 实际前缀跨度等于权重总和 |
| `PrefixMesh.next_weight_bound` | 相邻至多翻倍蕴含 `c_n≤Σ_{i<n}c_i+c_0` |
| `PrefixMesh.prefix_gap_bound` | §1.1：任意正整数权重序列满足两倍界时，所有前缀 gap≤首项 |
| `PrefixMesh.internal_run_bound` | 实际凸包内的连续缺失区间长度≤gap界−1 |
| `PrefixBounds.total_eq` | 冻结交错列的总和等于两列逐层总和 |
| `PrefixBounds.total_step` | `S_(n+1)=S_n+L_n` |
| `PrefixBounds.actual_prefix_encloses` | 实际地板前缀端点为 0、S_n |
| `PrefixBounds.actual_prefix_span` | 实际地板前缀跨度等于 S_n |
| `PrefixBounds.actual_prefix_gap` | §1.1：通过已证明的成对重排，得到原前缀 gap≤N |
| `PrefixBounds.total_ge_first` | `n≥2` 时 `S_n≥a_n`，直接归纳证明 |
| `PrefixBounds.uniform_cyclic_gap` | **(1.1)：`n≥2` 时实际 gcd 模前缀缺口 `h_n≤N−1`** |
| `PrefixBounds.internal_missing_run_bound` | §8：每个实际前缀 `[0,S_n]` 内的连续缺失段≤N−1 |
| `FECounting.translate_translate` | 连续平移等于平移量之和 |
| `FECounting.values_step` | `P_(n+1)=P_n∪(P_n+a_n)∪(P_n+b_n)∪(P_n+L_n)` |
| `FECounting.period_step` | `L_(n+1)=2L_n+w_n` |
| `FECounting.digitSum_bounds` | 实际两列数字和 `0≤w_n≤2` |
| `FECounting.digitSum_event_iff` | `w_n≠0` 当且仅当 n+1 是真实到达事件 |
| `FECounting.total_lt_period` | 正地板初值下 `S_n<L_n` |
| `FECounting.basic_copies_subset` | 两个基本复制集合都包含于下一实际前缀 |
| `FECounting.basic_copies_disjoint` | `P_n` 与 `P_n+L_n` 严格不交 |
| `FECounting.card_translate` | 平移保持不同整数值的个数 |
| `FECounting.growth_nonneg` | 从不交基本复制证明 `G_n≥0`，不是截断减法定义 |
| `FECounting.values_subset_period` | 全部 P_n 实际位于整数窗口 `[0,L_n)` |
| `FECounting.deficit_nonneg` | 不同和值的计数不超过窗口长度，故 `Q_n≥0` |
| `FECounting.padding_step` | `B_(n+1)=B_n+w_n` |
| `FECounting.padding_identity` | `B_n=M+N+Σ_{i<n}w_i` |
| `FECounting.padding_bound` | §8：`0<B_n<3N+2n` |
| `FECounting.deficit_step` | **(8.1)：`Q_(n+1)=2Q_n+w_n−G_n`** |
| `FECounting.deficit_zero` | 初值 `Q_0=M+N−1` |
| `FECounting.deficit_eq_holes` | Q_n 恰为 `[0,L_n)` 内实际缺失整数位置的个数 |
| `FECounting.growth_eq_newValues` | G_n 恰为下一前缀中、两基本复制之外新增整数值的个数 |

### 第六批当时的接口及未完成边界（历史记录）

- 统一缺口定理要求归一化整数初值 `0<b_0<a_0<2b_0`，不要求无理性、事件存在或
  长块。`actual_prefix_gap` 和内部缺失段界对所有 n 成立；`uniform_cyclic_gap`
  通过跨度投影到实际 gcd，需要 `n≥2`。没有混淆普通整数缺口与循环模缺口。
- 第六批用归纳直接证明 `S_n≥a_n`：先验证第2层，再使用地板递推推进。
  没有逐字形式化主稿更强的指数下界；所需跨度结论已经独立证明，不是额外前提。
- `values` 是原始索引有限子集的**不同整数和值**集合。四个平移采用 Finset 并集，
  重叠和值自动去重；只证明两个基本复制互不相交，没有声称四个复制均不相交。
- B、Q、G 都定义为整数差，非负性由数学证明导出。Q 和 G 的计数等价定理连接
  实际窗口缺失位置及实际新增和值，避免把代数递推与需要的对象脱节。
- **本批只完成 FE 的计数基础，不是 FE 衰减定理。** 还没有形式化周期缺失函数的
  边界变差 J、缺失段计数不等式 (8.2)、移位边界 (8.3)、变周期比较 (8.4)、
  非零事件边界 (8.5)，以及非重叠两步衰减和累计误差预算。

上面记录的 FE 义务现已在第七批完成，不是当前阻断。

## 第七批已编译定理与主稿对应（175个）

新增 29 个 Lean 模块，全部辅助定理均列入 `Audit.lean`。下表列出核心接口；
完整 358 项清单、逐项公理闭包及核心定理的实际 `#print` 输出见 `logs/axioms.log`。

| 核心声明（省略 `Dyadic354.`） | 已证明内容 |
|---|---|
| `FEMissingRuns.actual_holes_boundary_bound` | (8.2)：由实际内部缺失段界控制 Q 与单位边界 |
| `FEShift.variation_le_new_values` | (8.3)：旧列移位边界由真实新增和值控制 |
| `PeriodChange.actual_changing_period_bound` | (8.4)：不同周期函数的比较，显式支付末端 padding |
| `EventBoundary.actual_nonzero_boundary` | (8.5)：全部非零数字类型的单位边界估计 |
| `FERecurrence.potential_two_step`、`EventDecay.block_bound` | 非重叠事件块的衰减与累计误差预算 |
| `FE.deficit_exponential_bound` | FE：`Q_n ≤ C₀ 2^n exp(-a K_n)`，原稿常数 `C₀=2(M+N+10)`、`a=1/(64N)` |
| `FER.seed_exponential_bound` | FE-R：真实连续整数区间的最长宽度满足 `c₀ exp(a K_n) ≤ R_n+2`，原稿 `c₀` |
| `DBDigits.error_lt_budget`、`suffix_approximation` | (9.1)：真实后缀误差预算与不同索引的合法有限表示 |
| `DBCover.propagated_interval`、`DB.interval_complete` | 有限系数窗口与旧前缀拼接，形成足够宽的真实区间，推出完全性 |
| `DB.digit_propagation` | DB 增量对全部符合尺度的互素有理逼近成立，不限于有限参数测试 |
| `RationalWindows.before_crossing` | 从 Dirichlet 定理和首个好分母的最小性，构造前一精确小分母逼近 |
| `DBScale.advance_increment` | 定义实际分母 crossing 后，对每个 `n≥1` 得到 `K_f(n) ≥ K_n+(c₀/2)exp(aK_n)-3` |
| `CubicGrowth.no_eventual_cubic_advance` | 指数事件增量不能最终被三次深度增长容纳 |
| `BGWindows.arbitrarily_large_windows` | 从不完全性实际构造任意长窗口，同时满足有理逼近精度、`h²≤4T`、逐层误差界及事件对数稀疏性 |
| `BGExactLayers.nonexact_count` | (11.2)：非精确层个数至多 `hK_T+h`，包括最后 h 层 |
| `BGSparseCompact.irrational_separation` | 有界个联合二进制位置的比值属于全有理紧集，与固定无理数保持正距离 |
| `BGReturns.return_cost_unbounded` | (11.3) 所需的统一返回成本发散；不对共同乘数或 gcd 加界 |
| `BGGeometric.cost_bound`、`BGCapacity.eventual_capacity` | 足够多互不重叠的精确返回能放进同一窗口，累计事件成本严格超过总预算 |
| `BG.bounded_event_windows_complete` | BG：最终有界倍率事件窗口与无理比值推出归一化列完全性 |
| `BG.normalized_complete` | 已证明的倍率4后继事件界与 BG 相接，消去事件窗口前提 |

### 实现差异与验收边界

1. FE 的误差求和用势函数 `z_n+9(n+1)/2^n` 与非重叠块归纳处理。
   最终 FE 和 FE-R 的常数与原稿一致，没有把误差预算作为假设。
2. DB 直接构造每个目标整数的表示，不借用未经证明的“排序统计量移动”断言；
   原前缀与后缀的索引支持分离已经证明，重复和值不是重复使用同一索引。
3. §10–11 改用所有满足 `|θ-r|<1/den(r)²` 的好有理数。证明有界分母中只有
   有限个好有理数、无理数存在任意大好分母、首个跨越分母实际存在，以及所需
   前一小分母的精度。长窗口同时满足所有后续条件，不是给 BG 额外传入窗口假设。
   本批没有逐字形式化连分数编号 `q_j` 或原稿的 (10.2)；它们不是本实现的缺失依赖。
   `DB.digit_propagation` 的通用接口同样适用于满足其逼近条件的连分数收敛子。
4. 返回成本用真实二进制支持和全有理紧集证明，不另定义
   `min_c popcount((cp) OR (cq))`。所得结论直接量化任意精确返回，覆盖任意共同乘数。
5. 累计矛盾取返回次数 `K_T/k+1`，种子长度最终小于 `T^(3/4)`，几何增长至多
   `T^(1/8)`，剩余 `T^(1/8)` 吸收常数。它完成与原稿相同的 BG 结论，
   不要求逐项复现原稿 `T^(2/3)` 及特定返回次数下界。
6. 原始英文/中文主稿、证书、冻结 `Statements.lean`、工具链和依赖锁保持不变。
   源码无 `sorry`、自定义公理或 `native_decide`；传递公理审计是最终验收依据。

## 第八批已编译定理与主稿对应（23个）

新增 `Normalization.lean`、`SetBridge.lean`、`Main.lean`、
`UpstreamDefinitions.lean` 与 `UpstreamBridge.lean` 五个模块。
下表名称省略共同前缀 `Dyadic354.`；全部定理及其辅助引理均列入公理审计。

| 声明 | 对应内容 |
|---|---|
| `Normalization.term_shift` | 向上乘 `2^u` 的每项恰为原列第 `n+u` 项 |
| `Normalization.shifted_irrational` | 两列独立向上移位保持比值无理 |
| `Normalization.balance_larger`、`balance` | 正实数的相邻二幂界与无理性排除端点，只用非负整数移位得到严格比例 |
| `Normalization.common_shift`、`above_bound` | 克服地板误差，并使归一化保留尾项高于任意指定整数界 |
| `SetBridge.normalized_sorted_strictMono`、`normalized_injective` | 两列严格交错，原有 `a,b` 枚举虽非单调但数值仍单射 |
| `SetBridge.normalized_lower_bound` | 所有保留项都不小于首个较小项 |
| `SetBridge.indexed_to_set` | 单射数值序列的有限索引表示转换为无重复数值的有限集合表示 |
| `SetBridge.setComplete_mono`、`set_to_indexed` | 集合完全性保序，以及任意原列的集合表示转为合法索引表示 |
| `SetBridge.shifted_range_subset` | 独立移位后的两列确实取自原两列 |
| `erdos354_strong_completeness` | 对任意有限删除集，取高于其上界的归一化尾部并应用完整证明链 |
| `erdos354_part_i` | 冻结的全部正实数参数 #354(i)，没有额外前提 |
| `UpstreamBridge.floorMultiples_eq`、`interleave_eq` | 原列与上游精确定义的等式 |
| `UpstreamBridge.indexedComplete_iff`、`setComplete_iff`、`strongComplete_iff` | 两种表示、有限删除量词与上游定义之间的等价 |
| `UpstreamBridge.partITarget_iff` | 上游扩展量词排列与冻结 `PartI` 的双向等价 |
| `UpstreamBridge.erdos354_part_i_upstream`、`erdos354_strong_upstream` | 在上游精确定义类型中得到两个最终结论 |

### 上游与工具链边界

上游锁定提交使用 Lean/Mathlib 4.33.1，本工程继续使用 4.27.0，未升级。
七段上游定义逐字提取，原题正面 RHS 只增加命名空间限定；来源快照哈希、定义块
与目标文本均经自动检查，也实际与公开锁定源码进行在线字节核对。
这些语法核对之外，Lean 又证明定义及目标类型之间的等价，最终结论接受同一公理审计。
上游包含占位定理的完整文件仅以 `.txt` 保存为来源数据，没有被 Lean 导入。
未在完整上游 4.33.1 工程中构建，未创建上游 PR，不将这两件事报告为已经完成。

## 冻结目标的完成状态

- `Dyadic354.PartI`：任意正实数 α、β，无理比值，固定底数 2，地板交错列的有限索引和最终覆盖。
- `Dyadic354.StrongCompleteness`：删除任意有限个数值后的集合完全性。

它们仍保留为未改动的 `Prop` 定义，由 `Main.lean` 中两个已证明定理分别实现。
没有把原目标改弱，也没有通过增加类型类、占位定理或结论性前提完成它们。

## 验收边界与可选后续工作

1. 两个冻结数学目标已完成，没有剩余数学假设等待补证。第 (ii) 问不在本任务范围内。
2. 清洁重建只复用锁定依赖缓存，不复用本项目编译产物；没有从零重建 Mathlib，
   也未运行独立 checker 或 comparator。它们可用于进一步独立复核。
3. 全上游工程适配、工具链迁移和上游 PR 是后续集成事项，本次未执行。
4. 本实现使用已证明的有理逼近窗口及紧致返回接口。若要求逐字覆盖全部原稿表述，
   可另补 §6 的 N−1 次预算、`limsup≤3`、连分数编号版 (10.2) 和显式最小 popcount。
   它们不是最终 `PartI` 或 `StrongCompleteness` 的未完成依赖。

本批没有剩余编译阻断。历史失败与修复日志均保留；没有通过添加结论性前提绕过失败。
后续若遇到数学缺口，仍应独立报告，不能用工程构建成功代替未完成目标的证明。

## 发布状态

### 当前发布：全部冻结目标

2026-09-13 按维护者明确要求，第七、八批已提交成果已推送至 GitHub，
并将 `lean-formalization` 快进合并到 [`main`](https://github.com/Andrewyzzz/erdos354/tree/main)。
最终已验证源码提交为
[`59e5957ac8bf28623318cebec6c67b1a672ad49e`](https://github.com/Andrewyzzz/erdos354/commit/59e5957ac8bf28623318cebec6c67b1a672ad49e)。
该提交包含 #354(i)、强完全性和上游精确定义适配，以及 381 个定理的编译、
传递公理审计与清洁重建记录。本次只更新发布状态，不改动已验证源码或依赖。
未使用强制推送，未创建 Release、上游 PR 或论坛帖子。
原公开稿、归档和证书保持原样，不修改其候选稿及社区接受状态说明。

### 历史发布：第1–6批

第1–6批在本地 `lean-formalization` 分支开发，期间没有自动推送。
2026-09-13 按维护者明确要求，六批已验证成果已推送到 GitHub 的
[`lean-formalization` 分支](https://github.com/Andrewyzzz/erdos354/tree/lean-formalization)，
已验证源码提交为 `04c0593bba303281787f2bccc5450a3e879dcfd6`。
当时的推送包括源代码、锁定依赖、状态文件和实际编译/公理审计日志。
原公开稿件与证书保持不变，当时未合并到 `main`，未创建 Release，未发论坛帖子。
当时公开的是分阶段形式化进展，不是整个 #354(i) 的完成证明。

第七批 FE／DB／BG 提交为 `1e6e6d93661dbaa67700ee77097901ea66f276cd`。
第七、八批此前只保存在本地；现已按上方“当前发布”记录推送并合并。
