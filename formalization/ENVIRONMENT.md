# 实际形式化环境

记录日期：2026-09-12。第一批命令见 `logs/environment.log`，第二批实际复核见
`logs/mesh-environment.log`。

- 执行位置：本机 macOS 26.5.1，Apple Silicon / arm64。
- 原稿基准提交：`dcdc3c255189ab4e0f9bbf9abea2ca0a3758de06`。
- 第二批起点：第一批提交 `0f638801c6220866661581e5848eae7db87798a1`。
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
它包含初始 18 个定理的审计。第一批最终为 20 个定理；第二批增加 31 个定理，
累计 51 个。当前验收以 `logs/build.log`、`logs/axioms.log`、
`logs/verification.json` 为准。第一批最终日志仍保存在其提交与第一批交付包中。

独立目录重建见 `logs/fresh-build.log`、`logs/fresh-axioms.log`、
`logs/fresh-verification.json`。该检查重新编译本项目的源码，复用同版本 Mathlib
编译缓存，不宣称重建了整个 Lean/Mathlib，也未运行外部 checker 或 comparator。

早期 `basic*.log` 和 `certificate*.log` 保留了实际编译修复过程。最初的问题涉及
未展开的锥条件、缺少库导入、保留标识符及化简顺序，均已解决；这些历史日志不表示
最终构建状态。

`mesh-cyclic-01.log`、`mesh-02.log`、`mesh-03.log` 记录第二批的实际编译修复。
问题为策略风格检查、数值转换的类型推断及归纳基步类型推断，均已修复；
没有修改数学前提或原始主稿来绕过失败。
