# 第二批状态

**证书模块、三个基础网格引理及逐步传播推论已形式化；#354(i) 与集合强完全性尚未形式化完成。**

实际证书由 Lean 内核计算核验，通过通用 soundness 定理得到全部合法整数参数上的
系数覆盖与六项子集和语义。第二批证明主稿 Lemma 2.1、2.2、2.3，并补齐最长缺失段、
实际相邻点距离与窗口表述之间的连接。有限数据使用 `decide +kernel`，累计 51 个本地定理的
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

## 固定但未证明的目标

- `Dyadic354.PartI`：任意正实数 α、β，无理比值，固定底数 2，地板交错列的有限索引和最终覆盖。
- `Dyadic354.StrongCompleteness`：删除任意有限个数值后的集合完全性。

它们是 `Prop` 定义，不是已证明定理。工程中没有以占位符实现的主定理。
本批借用了上游定义的独立副本；与安装后的 Formal Conjectures 工程进行直接类型
对接仍未完成，来源和定义对应见 `UPSTREAM.md`。

## 后续数学义务

1. §1 与 §3：地板递推、到达层事件、实际前缀；把本批六个局部位置嵌入原序列索引。
2. §3.1–3.2：旧系数区间、实际前缀代表大小、合法不交索引拼接；本批尚未证明这些表示区间。
3. §4–6：缩短节点窗口、由实际子集和构造初始整数网格、永久下降及事件倍率有界。
4. §8–11：完整 FE、DB、BG，变周期边界、连分数匹配层和返回成本极限。
5. §1、§7：合法向上截尾、去重、有限删除、两种完全性及上游原题的最终连接。

本批没有剩余编译阻断，也未发现三个有限网格引理中的数学缺口。`propagate_iterate`
是给定初始网格后的通用保持定理，尚不构成第3–6节的永久下降链证明。此结论不评价上述尚未
形式化的无限论证。后续若出现阻断，应单独保存最小失败文件、目标上下文和缺失引理。

## 发布状态

本批在本地 `lean-formalization` 分支开发。原公开稿件与证书保持不变；未推送本批
到 GitHub，未创建 Release，未发论坛帖子。发布前还需要按相应里程碑明确成果范围。
