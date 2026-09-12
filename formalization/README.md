# Erdős 354(i): first Lean formalization batch

本批已完成有限模板证书的 Lean 内核形式化。**整篇 #354(i) 与集合强完全性尚未证明。**
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
`verify.py` 默认构建根模块 `Dyadic354`，它导入目标定义、证书及公理审计。
脚本再次执行 `Audit.lean`，核对全部本地定理的审计清单，检查实际公理闭包；
缺少输出或出现允许列表以外的公理都会以非零退出码结束。

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

这里的六项是主稿 §3 给出的代数表达式。把它们嵌入实际地板序列、与旧前缀和
精确倍增块拼接、构造永久网格，仍属于后续工作。

## Source map

| File | Purpose |
|---|---|
| `Dyadic354/Statements.lean` | 原题与强完全性的固定定义；显式阈值等价式 |
| `Dyadic354/Basic.lean` | 有限子集和值与整数锥引理 |
| `Dyadic354/Certificate.lean` | 通用检查器、掩码语义、区间链及正确性证明 |
| `Dyadic354/CertificateData.lean` | 原始 JSON 的可重生成数据与实际证书定理 |
| `Dyadic354/Audit.lean` | 目标类型输出与全部已完成定理的公理审计 |
| `scripts/generate_data.py` | 数据翻译及与 JSON 的一致性检查 |
| `scripts/verify.py` | 构建、公理允许列表、独立目录重建 |

上游定义来源与许可见 [UPSTREAM.md](UPSTREAM.md)。公开稿件及原始证书保持原样。
