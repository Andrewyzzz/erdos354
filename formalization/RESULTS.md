# 最终验收摘要

2026-09-13。本地 Lean 形式化验收：**PASS**。

## 已完成的数学目标

- `Dyadic354.erdos354_part_i : PartI`：任意正实数 α、β，比值无理，底数固定为 2；
  每个充分大的整数均为交错列的合法有限索引和。
- `Dyadic354.erdos354_strong_completeness : StrongCompleteness`：从原始非零数值集
  删除任意有限数值集后，每个充分大的整数仍可表示为不同剩余数值的有限和。

两个目标定义均与第一批冻结版本相同。最终定理没有额外归一化、FE、DB、BG、
永久下降、长窗口或事件间隔假设。完整证明在 [Main.lean](Dyadic354/Main.lean)，
确切目标定义在 [Statements.lean](Dyadic354/Statements.lean)。

## 实际验收

| 检查 | 结果与记录 |
|---|---|
| 全量默认构建与全部公理审计 | PASS，381 个定理；[verification.json](logs/verification.json) |
| 独立源码目录重建与再次公理审计 | PASS，381 个定理；[fresh-verification.json](logs/fresh-verification.json) |
| 两次验收源码哈希与逐项公理闭包 | 完全一致 |
| 清洁目录与交付源码/脚本/上游数据比较 | 退出码 0；[比较日志](logs/final-clean-source-match.log) |
| 原发布包输入完整性 | 36 个文件哈希匹配；[完整性日志](logs/eighth-batch-input-integrity.log) |
| 锁定上游来源与精确目标 | 在线字节核对及离线定义检查通过；[来源日志](logs/upstream-provenance-online.log) |

所有定理只依赖 `propext`、`Classical.choice`、`Quot.sound` 的子集。
编译源码无 `sorry`、自定义公理、`native_decide` 或跳过内核检查机制。
最终主定理的实际 `#print` 与传递公理输出保存在 [axioms.log](logs/axioms.log)；
清洁重建输出在 [fresh-axioms.log](logs/fresh-axioms.log)。

## 范围与信任边界

- 本工程仍使用 Lean 4.27.0 和锁定的 Mathlib 提交，未升级依赖。
- 清洁重建不复用本项目编译产物，但复用锁定依赖缓存；没有从零重建 Mathlib，
  没有运行外部独立 checker 或 comparator。
- 上游七段定义逐字提取，正面第 (i) 问的 RHS 精确核对，并由 Lean 证明类型等价及
  对应结论。没有导入上游占位定理；没有在其完整 Lean 4.33.1 工程中构建。
- 部分中间证明采用已证明的替代实现，而非逐行照搬原稿，见 [STATUS.md](STATUS.md)。
- 第 (ii) 问、上游 PR、社区接受与期刊发表不属于本次完成结论。
- 原公开稿及归档保持原字节；2026-09-13 按维护者明确要求，第七、八批成果已推送，
  并将 `lean-formalization` 快进合并到 `main`。已验证源码提交为
  [`59e5957`](https://github.com/Andrewyzzz/erdos354/commit/59e5957ac8bf28623318cebec6c67b1a672ad49e)。

复现命令、完整模块说明见 [README.md](README.md)，环境与依赖记录见
[ENVIRONMENT.md](ENVIRONMENT.md)，上游适配细节见 [UPSTREAM.md](UPSTREAM.md)。
