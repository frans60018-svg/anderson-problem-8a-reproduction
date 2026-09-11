# 项目文件导航

更新日期：2026-09-11。整理保留现有源码路径、导入、工具和运行产物，
通过统一入口区分当前状态、历史记录和外部源码。

## 给首次阅读者

1. [README](../README.md)：研究问题、结果与两条证明轨。
2. [当前状态](CURRENT_STATUS.md)：已完成内容、五个外部公理和剩余事项。
3. [来源说明](../UPSTREAM_PROVENANCE.md)：上游提交及本次贡献边界。
4. [信任边界](../TRUST_BOUNDARY.md)：最终定理实际依赖哪些公理。
5. [验证报告](../VERIFICATION_REPORT.md)：本地验证方法与 Comparator 范围。

## 仓库各层

| 位置 | 用途 |
|---|---|
| `Anderson/`、`Anderson.lean` | 引入的上游完整证明，非本次独立生成 |
| `StrictReproduction.lean` | 规范主定理入口，只导入规范轨 |
| `StatementAudit.lean`、`StrictAxiomAudit.lean` | 声明与规范公理审计 |
| `AxiomAudit.lean` | 同时显示历史和规范主定理的公理闭包 |
| `Run202608192034.lean`、同名目录 | 历史 Archon 证明与五个假设 |
| `blueprint/`、`.leandag/`、`source_blueprint.md` | 历史轨蓝图与图，不是 canonical DAG |
| `.archon/` | 当前摘要以及日期化开发记录 |
| `references/` | 公开参考文献信息、短摘录和检索记录 |
| `LICENSES/`、`THIRD_PARTY_NOTICES.md` | 上游许可证和署名 |
| `scripts/`、`.github/workflows/` | 已有本地检查和远程 CI 配置 |
| `docs/workspace/` | 本地外层工作区说明的发布快照 |

## 本地完整工作区

Git 仓库根位于：
`03_full_pipeline_reproduction/03_archon_runs/projects/run-20260819-2034/`。
外层 `Anderson论文复现/` 另有原论文、独立上游 checkout 和复现工具：

| 位置（相对于外层工作区） | 用途 |
|---|---|
| `论文.pdf` | 原自动化数学研究论文，本地保留 |
| `Anderson-Conjecture/` | 上游参考 checkout 及其 Comparator 环境 |
| `证明蓝图对照表.md` | 上游关键声明级阅读对照，非完整 DAG |
| `03_full_pipeline_reproduction/01_problem_input/` | 固定问题与输入政策 |
| `03_full_pipeline_reproduction/02_rethlas_runs/` | Rethlas 运行记录 |
| `03_full_pipeline_reproduction/03_archon_runs/` | Archon 运行和当前 Git 仓库 |
| `03_full_pipeline_reproduction/04_comparison/` | 上游结果与本次成果对照 |
| `03_full_pipeline_reproduction/05_fallbacks/` | 替代与辅助输入披露 |
| `03_full_pipeline_reproduction/tools/` | 工具源码和本地环境 |

外层说明的公开快照放在 `docs/workspace/`；其中相对路径按原工作区解释，
不是发布仓库内的可执行路径。下载书籍、论文全文、缓存和私密配置只保留在本地。
