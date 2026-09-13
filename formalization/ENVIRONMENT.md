# 实际形式化环境

记录日期：2026-09-13（Asia/Shanghai）。第一批命令见 `logs/environment.log`，
第二批复核见 `logs/mesh-environment.log`，第三批复核见
`logs/third-batch-environment.log`，第四批实际复核见
`logs/fourth-batch-environment.log`，第五批实际复核见
`logs/fifth-batch-environment.log`，第六批实际复核见
`logs/sixth-batch-environment.log`，第七批实际复核见
`logs/seventh-batch-environment.log`，第八批实际复核见
`logs/eighth-batch-environment.log`；命令日志使用 UTC 时间。

- 执行位置：本机 macOS 26.5.1，Apple Silicon / arm64。
- 原稿基准提交：`dcdc3c255189ab4e0f9bbf9abea2ca0a3758de06`。
- 第二批起点：第一批提交 `0f638801c6220866661581e5848eae7db87798a1`。
- 第三批起点：第二批提交 `16e0de8ba8dd9f81d2e04d7834ed29ddaca1e7eb`。
- 第四批起点：第三批提交 `d685bb3df0cb05190c31b7a92c2c7271f053580d`。
- 第五批起点：第四批提交 `e3985208220a96030f454d3ab5e82ac42135a53c`。
- 第六批起点：第五批提交 `ea7ad5fd1eb85db223878a6c92f37d77868532ee`。
- 第七批起点：前六批发布记录提交 `f6c5d2ba8cbca95427ae6aea854d11116f06cd55`。
- 第八批起点：FE／DB／BG 提交 `1e6e6d93661dbaa67700ee77097901ea66f276cd`。
- 开发分支：`lean-formalization`。起始工作树干净，所有新增内容位于 `formalization/`。
- 实际 Lean：`4.27.0`，commit `db93fe1608548721853390a10cd40580fe7d22ae`。
- 实际 Lake：`5.0.0-src+db93fe1`，使用 Lean 4.27.0。
- Mathlib：`a3a10db0e9d66acbebf76c5e6a135066525ac900`，对应 `v4.27.0`。
- `lake-manifest.json` 锁定全部 9 个依赖；实际 Git HEAD 均与锁定值一致，依赖源码没有已跟踪修改。
- 本机还安装 Lean 4.32.0，但本项目通过 `lean-toolchain` 固定使用 4.27.0。

Elan 输出中有一次查询默认 stable 最新版本失败的警告。项目覆盖版本仍明确为
4.27.0，已成功执行构建，没有升级工具链。

## Frozen inputs

| File | SHA-256 |
|---|---|
| `proof/PROOF.md` | `8662891ac64f4ed2805a889d087afc7848667b1519192bf368ebdefba30bbdd2` |
| `proof/PROOF.zh-CN.md` | `a424bb9c470e0303bf9529add146911c1b2717375ecb458b4a0cafae450aa618` |
| `certificate/templates.json` | `3293a4fb061ba625ba1f11788dca751920a182d26d60d6298b31a058c065c048` |
| `certificate/check_templates.py` | `862b5ddbb55d134336029977961c4cf0391ff67024f2946b039ca584cab1b98d` |

交接任务书的英文主稿哈希 `f17d67…` 对应修改贡献者署名前的提交；与本基准的主稿
差异仅为署名。这里记录真实输入，未把两份不同字节的文件视作同一冻结版本。

## Cache and build

本机复用已有 `erdos1-reproduction/lean/.lake/packages` 的 Mathlib 4.27.0 缓存。
本项目 `.lake/packages` 是本地符号链接，受 `formalization/.gitignore` 排除；
该绝对路径不进入 Lake 配置或依赖锁文件。下载后的工程可以用 `lake exe cache get`
恢复锁定依赖，源代码不依赖上述本地路径。

首个完整构建成功记录为 `logs/certificate-04.log`：`lake build` 退出码 0。
它包含初始 18 个定理的审计。第一批最终为 20 个定理；第二批增加 31 个，
第三批增加 32 个，第四批增加 44 个，第五批增加 21 个，第六批增加 35 个，
第七批增加 175 个，第八批增加 23 个，累计 381 个。
当前验收以 `logs/build.log`、`logs/axioms.log`、
`logs/verification.json` 为准。前七批最终日志仍保存在对应提交与交付包中。

独立目录重建见 `logs/fresh-build.log`、`logs/fresh-axioms.log`、
`logs/fresh-verification.json`。该检查重新编译本项目的源码，复用同版本 Mathlib
编译缓存，不宣称重建了整个 Lean/Mathlib，也未运行外部 checker 或 comparator。

早期 `basic*.log` 和 `certificate*.log` 保留了实际编译修复过程。最初的问题涉及
未展开的锥条件、缺少库导入、保留标识符及化简顺序，均已解决；这些历史日志不表示
最终构建状态。

`mesh-cyclic-01.log`、`mesh-02.log`、`mesh-03.log` 记录第二批的实际编译修复。
问题为策略风格检查、数值转换的类型推断及归纳基步类型推断，均已修复；
没有修改数学前提或原始主稿来绕过失败。

第三批实际迭代保存在 `coefficient-interval-*`、`representations-*`、
`node-representations-*`、`node-window-*`、`initial-mesh-*`、`permanent-mesh-*`
日志中。初始网格最终模块构建见 `initial-mesh-06.log`，永久网格最终模块构建见
`permanent-mesh-04.log`；上述历史失败均已修复。过程中 Lean 对失败目标显示的
内部占位项不是源代码证明，验收只接受最终全量构建及公理闭包。

`logs/third-batch-input-integrity.log` 实际检查了原发布稿的 36 个文件哈希，全部匹配。
第三批没有变更公开主稿、原始 JSON、已有目标定义或工具链与依赖锁。

第四批实际迭代保存在 `floor-sequence-*`、`pair-reindex-*`、`exact-block-*`、
`floor-descent-*`、`block-length-*` 日志中。`floor-descent-04.log` 记录实际地板序列的
到达层永久下降模块通过；`block-length-02.log` 记录长度条件模块通过。
全量构建导入全部新模块及全部公理审计，验收不是只构建旧证书目标。

`logs/fourth-batch-input-integrity.log` 再次核对全部 36 个原发布文件哈希并通过。
第四批没有变更公开主稿、原始证书、冻结原题定义、工具链或依赖锁；9 个依赖的实际
Git HEAD 全部匹配锁定值，且没有已跟踪修改。已证明部分的公理依赖仍仅为允许的三个
标准公理的子集。

第五批模块编译见 `unit-mesh-01.log`、`low-gap-01.log`、`event-gaps-01.log` 和
`event-infinitude-02.log`。`event-infinitude-01.log` 中实数不等式的策略选用问题
已经修复；最终构建导入所有第五批模块，全部辅助定理也纳入公理审计。
`logs/fifth-batch-input-integrity.log` 检查全部 36 个原发布文件哈希并通过。
第五批工具链和全部 9 个依赖版本未改变，依赖源码无已跟踪修改；公开稿、证书和
冻结的原题定义保持原样。新成果仍为条件完全性与反证路线中的事件倍率界，
不是整个 #354(i) 的验证结果。

第六批实际编译迭代见 `prefix-mesh-01.log`、`prefix-bounds-01.log` 和
`fe-counting-*`。初轮下标/重排展开、有限集接口与严格风格检查问题已修复。
`fe-counting-03.log` 同时记录更新后的前缀网格、实际前缀界及初版 FE 计数模块通过；
计数含义补充的最终模块构建见 `fe-counting-04.log`。
全量及独立目录验收包含全部新模块和全部 183 个定理，不仅是旧证书构建。

`logs/sixth-batch-input-integrity.log` 再次检查全部 36 个原发布文件哈希并通过；
工具链、9 个依赖实际提交、冻结原题定义与公开主稿保持不变。
本批完成的是统一缺口界及 FE 的精确有限计数基础，不宣称 FE 衰减估计已经通过验证。

## 第七批：FE／DB／BG

本批新增 29 个 Lean 模块、175 个定理，完成 FE 与 FE-R、DB 增量、实际长窗口、
统一精确返回成本与 BG 累计矛盾，最终得到 `BG.normalized_complete`。
该定理只要求归一化地板初值和比值无理；它并非任意正参数的原题，也未证明集合强完全性。
本批没有修改工具链、依赖锁、冻结目标定义或原稿来取得这一结论。

关键模块成功编译记录包括 `fe-main-01.log`、`fe-seed-03.log`、`db-main-05.log`、
`bg-returns-03.log`、`bg-windows-02.log`、`bg-capacity-04.log` 和 `bg-final-02.log`。
历史失败日志保留完整目标上下文，问题涉及类型转换、库接口、归纳/算术证明及严格风格检查；
最终均已修复。`fe-db-bg-core-audit.log` 是中间检查点，不代替最终 358 项全量审计。

`logs/seventh-batch-input-integrity.log` 再次核对全部 36 个原发布文件哈希，全部匹配。
`logs/seventh-batch-environment.log` 确认 Lean 4.27.0 和全部 9 个依赖实际提交匹配锁定值，
依赖源码没有已跟踪修改。最终验收仍以 `verification.json`、`fresh-verification.json`
及相应实际日志为准；清洁重建复用依赖缓存，不宣称从零重建 Mathlib 或运行外部 checker。

## 第八批：一般参数、强完全性与上游目标

本批增加 23 个定理，完成只向上取尾的归一化、无重复数值证明、有限删除集上界
规避及集合/索引表示连接。`Main.lean` 实现未改动的 `PartI` 与 `StrongCompleteness`。
`UpstreamBridge.lean` 实现精确上游定义中的正面命题与集合强完全性。
所有新模块都由默认根目标实际导入；最终验收不是只构建旧模块。

实际编译迭代保存在 `normalization-01.log`、`main-*.log`；初轮问题涉及严格风格检查、
函数参数个数、重写顺序及局部缩写的算术识别，不是通过添加数学前提修复。
来源检查见 `upstream-provenance-offline.log`、`upstream-provenance-online.log`；
首次沙箱 DNS 失败日志保留，后续只读网络复核成功。

上游锁定提交的真实工具链为 Lean 4.33.1。没有安装或升级本工程工具链；
七段上游定义逐字提取，在现有 Lean 4.27.0 中编译，并核对精确 RHS 和内核类型等价。
这不是完整上游 checkout 的构建，不声称已完成上游 PR 集成。完整来源说明见 `UPSTREAM.md`。

`eighth-batch-input-integrity.log` 再次确认 36 个原发布文件哈希全部匹配。
`eighth-batch-environment.log` 确认现有工具链、全部 9 个依赖实际提交和依赖源码未变。
最终全量与独立源码目录重建的 381 项验收见 `verification.json`、`fresh-verification.json`；
对应日志包含最终目标的实际 `#print` 与全部传递公理输出。
`logs/final-clean-source-match.log` 另外逐项比较了清洁目录与交付工作树的源码、
脚本和上游来源数据，退出码 0；只排除了编译缓存、日志、Markdown 说明和 Python 缓存。
