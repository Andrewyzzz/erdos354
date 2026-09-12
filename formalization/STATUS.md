# 第四批状态

**已把局部下降接到实际地板序列、实际 gcd 模数与到达层事件，并证明块长门槛；#354(i) 与集合强完全性尚未形式化完成。**

实际证书由 Lean 内核计算核验，通过通用 soundness 定理得到全部合法整数参数上的
系数覆盖与六项子集和语义。第二批证明主稿 Lemma 2.1、2.2、2.3，并补齐最长缺失段、
实际相邻点距离与窗口表述之间的连接。第三批增加主稿 §3–4 的有限表示链及 §5 的局部
代数投影链，共增加 32 个定理。第四批增加 44 个定理，完成地板递推、成对重排、
实际局部块、gcd 坐标、条件永久下降及长度估计。有限数据使用 `decide +kernel`，累计 127 个本地定理的
传递公理依赖均为 `propext`、`Classical.choice`、`Quot.sound` 的子集。
最终构建与审计见 `logs/verification.json`，独立目录重建见
`logs/fresh-verification.json`；完整实际输出保存在同目录的日志。

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

### 当前最强结论及其前提

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
**长间隔的存在/累计矛盾、低缺口推出完全性与无限事件链仍未完成。**
因此第3里程碑已进一步推进，但仍不能称 §2–6 已全部形式化，更不能称 FE/DB/BG 已完成。

## 固定但未证明的目标

- `Dyadic354.PartI`：任意正实数 α、β，无理比值，固定底数 2，地板交错列的有限索引和最终覆盖。
- `Dyadic354.StrongCompleteness`：删除任意有限个数值后的集合完全性。

它们是 `Prop` 定义，不是已证明定理。工程中没有以占位符实现的主定理。
本批借用了上游定义的独立副本；与安装后的 Formal Conjectures 工程进行直接类型
对接仍未完成，来源和定义对应见 `UPSTREAM.md`。

## 后续数学义务

1. §1：无理比值蕴含事件集无限；固定前缀网格界及主稿的统一 `h_n≤N−1` 界尚未证明。
2. §5–6：低缺口/单位网格推出完全性，不相交更新时刻、有限次严格下降及事件倍率有界。
3. §1、§7：一般正实数参数的合法向上归一化、截尾、去重、有限删除；本批仍以已归一化初值为条件。
4. §8–11：完整 FE、DB、BG，变周期边界、连分数匹配层和返回成本极限。
5. 两种完全性及上游 Formal Conjectures 原题的最终连接与陈述核对。

本批没有剩余编译阻断。已检查部分没有发现数学缺口；上一批标出的未来枚举顺序与
局部权重接口已通过显式证明补齐。编译修复涉及地板表达式一致性、缩写展开、
依赖非空证明的等式改写和严格风格检查，未改弱数学命题。
上述尚未完成的无限论证没有因此得到验证。后续若出现阻断，应单独保存最小失败文件、
完整目标上下文和缺失引理。

## 发布状态

本批在本地 `lean-formalization` 分支开发。原公开稿件与证书保持不变；未推送本批
到 GitHub，未创建 Release，未发论坛帖子。发布前还需要按相应里程碑明确成果范围。
