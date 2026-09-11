# Anderson 论文复现记录

## 最新状态（2026-09-11）

当前入口：[项目导航](03_full_pipeline_reproduction/03_archon_runs/projects/run-20260819-2034/docs/PROJECT_GUIDE.md)、
[完成边界](03_full_pipeline_reproduction/03_archon_runs/projects/run-20260819-2034/docs/CURRENT_STATUS.md)。
完整规范证明是上游源码整合成果；历史轨仍有 5 个外部公理（主定理依赖 4 个）。
Comparator 的成功记录来自独立上游 checkout；远程 CI 应按发布提交检查。

完整流程工作区现已建立独立规范入口
`Run202608192034.andersonProblem8a`：它与发布版 challenge statement 完全
一致，canonical 源码零 `sorry`、零项目自定义公理，完整构建通过，并已通过
发布版 Comparator 的 Lean kernel 重放。此前独立推进的 257 节点 Archon 轨
继续保留，用于展示从文献路线到中间 Lean 证明的工作；官方完整源码的最终
整合已单独记录来源、许可证和 fallback，未被冒充为独立生成。

权威状态见：

- `03_full_pipeline_reproduction/STATUS.md`
- `03_full_pipeline_reproduction/03_archon_runs/projects/run-20260819-2034/README.md`
- `03_full_pipeline_reproduction/03_archon_runs/projects/run-20260819-2034/VERIFICATION_REPORT.md`

本文件夹整理了论文 `Automated Conjecture Resolution with Formal Verification` 的本地阅读与复现工作。当前重点复现的是论文公开的 Lean 4 形式化证明结果：证明存在一个弱拟完备但不是拟完备的 Noetherian 局部环，从而否定回答 Anderson 2014 年提出的交换代数问题。

## 文件夹结构

```text
Anderson论文复现/
├── README.md
├── 证明蓝图对照表.md
├── 03_full_pipeline_reproduction/
├── 论文.pdf
├── run-verify.sh
└── Anderson-Conjecture/
    ├── Anderson/                 # 形式化证明主体
    ├── Challenge.lean            # 人类可读的主定理规格，含 intentional sorry
    ├── Anderson.lean             # Lean 根模块
    ├── Anderson/Main.lean        # main_theorem 的最终拼装
    ├── lakefile.toml             # Lake 项目配置
    ├── lake-manifest.json        # 依赖锁定文件
    ├── lean-toolchain            # Lean 版本锁定
    ├── config.json               # Comparator 验证配置
    ├── verify-local.sh           # 仓库内一键验证脚本
    ├── .tools/                   # 本地 Go 工具链和包装脚本
    ├── landrun/                  # Comparator 沙箱依赖
    ├── lean4export/              # Lean 导出器
    └── comparator/               # Lean Comparator
```

## 论文讲了什么

论文提出了一个自动化数学研究框架，把自然语言数学推理和形式化验证结合起来：

- `Rethlas`：非形式化推理代理，负责搜索相关数学定理、拆分目标、生成候选证明。
- `Archon`：形式化验证代理，负责把候选证明转成 Lean 4 项目，并通过任务分解、反复修补和 proof synthesis 让证明被机器检查通过。
- `Matlas` 和 `LeanSearch`：分别服务于非形式化和形式化阶段的定理检索。

论文最主要的成果是自动解决一个研究级交换代数开放问题：Anderson 2014 年问题 8a 问“弱拟完备局部环是否一定拟完备”。作者的系统构造并形式化证明了一个反例：存在弱拟完备、Noetherian、局部，但不是拟完备的环。

最直接、可验证的复现目标是运行作者公开的 Lean 4 形式化证明仓库，并使用 Comparator 检查完整证明确实证明了 `Challenge.lean` 中的主定理声明。

## 本机已配置环境

本地配置如下：

- Git：系统已有。
- Python：系统已有，版本为 `Python 3.9.6`。
- Lean/Elan：已安装到用户目录 `~/.elan`。
- Lean 工具链：`leanprover/lean4:v4.29.0-rc8`。
- Mathlib：已按仓库锁定版本下载预编译缓存。
- Go：下载 Go 官方 macOS ARM64 压缩包并解压到项目本地目录。
- Comparator 依赖：已在 `Anderson-Conjecture/` 内构建 `landrun`、`lean4export`、`comparator`。

关键版本：

```text
Lean: leanprover/lean4:v4.29.0-rc8
Mathlib: v4.29.0-rc8
Go: go1.26.5 darwin/arm64
```

## 一键复现

从终端运行：

```bash
/Users/sy/Desktop/Anderson论文复现/run-verify.sh
```

该脚本会执行两步：

1. `lake build`：用 Lean 构建整个 `Anderson` 形式化证明项目。
2. `lake env comparator config.json`：使用 Comparator 检查 `Anderson` 中的完整证明是否严格匹配 `Challenge.lean` 中的主定理声明，并检查允许的公理集合。

成功时末尾应看到：

```text
Build completed successfully (2705 jobs).
Lean default kernel accepts the solution
Your solution is okay!
```

`Challenge.lean` 中的 `sorry` 警告是正常现象。这个文件是短规格文件，用来描述需要被证明的主定理；Comparator 会确认 `Anderson` 项目中的完整证明确实填补了这个声明。

## 手动复现步骤

如果不使用一键脚本，可以手动运行：

```bash
cd /Users/sy/Desktop/Anderson论文复现/Anderson-Conjecture
./verify-local.sh
```

或者展开为：

```bash
cd /Users/sy/Desktop/Anderson论文复现/Anderson-Conjecture
export PATH="$HOME/.elan/bin:$PWD/landrun:$PWD/.tools/bin:$PWD/lean4export/.lake/build/bin:$PWD/comparator/.lake/build/bin:$PWD/.tools/go/bin:/usr/bin:/bin:/usr/sbin:/sbin"
lake build
lake env comparator config.json
```

## 本次已验证结果

本机已经成功跑通两层验证：

1. Lean 构建验证：

```text
Build completed successfully (2705 jobs).
```

2. Comparator 验证：

```text
Running Lean default kernel on solution.
Lean default kernel accepts the solution
Your solution is okay!
```

这说明当前本地环境已经可以复现论文公开的形式化证明结果。

## 第二层证明路线复现

本文件夹已补充：

```text
证明蓝图对照表.md
```

这份文档把 `INFORMAL_RAW_OUTPUT.md` / `Mathematical_Proof.pdf` 中的非形式化证明步骤，逐段对应到 `Anderson/` 下的 Lean 文件、关键定理声明和最终主定理拼装。它用于理解“证明思路如何落到严格形式化证明结构上”。

当前第二层复现覆盖：

- 非形式化证明蓝图的主要步骤；
- `T = C[[x,y,z]]/(x^2-yz)` 的 Lean 构造；
- Jensen 构造如何在 Lean 中封装成 `jensen_special_case`；
- Farley/Anderson 判别准则在 Lean 中的对应定理；
- `A` 弱拟完备、存在坏商环、`A` 不拟完备的最终拼装；
- `Challenge.lean` 与 `Anderson/Main.lean` 的主定理对应关系。

第二层文档自身只覆盖路线对照。后续已执行 Rethlas 和 Archon 辅助复现，
其结果和 fallback 见第三层工作区。

建议阅读顺序：

1. 先读 `证明蓝图对照表.md`。
2. 再读 `Anderson-Conjecture/Challenge.lean`，确认主定理规格。
3. 读 `Anderson-Conjecture/INFORMAL_RAW_OUTPUT.md` 和 `Anderson-Conjecture/Mathematical_Proof.pdf`，理解非形式化证明。
4. 从 `Anderson-Conjecture/Anderson/Main.lean` 反向追踪关键依赖。
5. 重点核对 `Anderson/Basic.lean`、`Anderson/QuasiCompleteRing/QuasiCompleteRing.lean`、`Anderson/CompleteDomain/*`、`Anderson/Jensen/*`。

## 第三层完整流程复现工作区

本文件夹已建立：

```text
03_full_pipeline_reproduction/
```

该工作区用于尽可能按照原论文顺序推进：

```text
数学问题输入
→ Rethlas 非形式化证明搜索与验证
→ Archon 形式化项目生成、证明填充与 polish
→ lake build
→ Comparator 验证
→ 与官方 Anderson-Conjecture 对比
```

关键文件：

- `03_full_pipeline_reproduction/README.md`：工作区总说明。
- `03_full_pipeline_reproduction/experiment_protocol.md`：完整实验协议和 fallback 规则。
- `03_full_pipeline_reproduction/STATUS.md`：阶段状态追踪。
- `03_full_pipeline_reproduction/01_problem_input/anderson_problem.md`：Rethlas 阶段的原始问题输入。
- `03_full_pipeline_reproduction/01_problem_input/input_policy.md`：输入材料边界，防止把官方成品证明提前喂给自动流程。
- `03_full_pipeline_reproduction/04_comparison/comparison_template.md`：候选项目与官方项目的对比模板。
- `03_full_pipeline_reproduction/05_fallbacks/fallback_log.md`：记录所有使用官方结果替代的地方。

上游证明的本地构建与审计已完成，辅助流程已产出蓝图和中间形式化成果。
独立闭合历史轨、规范 DAG、逐句论文映射和自包含远程 Comparator 尚未完成。
本轮已获授权发布 GitHub，公开仓库仅包含必要成果与说明。

## 参考链接

- Anderson-Conjecture: https://github.com/frenzymath/Anderson-Conjecture
- Archon: https://github.com/frenzymath/Archon
- Rethlas: https://github.com/frenzymath/Rethlas
- Lean: https://lean-lang.org/
- Elan: https://github.com/leanprover/elan
- Comparator: https://github.com/leanprover/comparator
- Go Downloads: https://go.dev/dl/
