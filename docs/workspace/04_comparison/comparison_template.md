# Candidate vs Official Comparison

> 2026-09-11：此表为主要结果和关键声明级对比，不是逐句论文映射或
> 声明依赖 DAG。Comparator 的 Pass 指独立上游 checkout 的本地运行。
> 规范代码来自上游，历史轨仍有五个外部公理；远程 CI 状态不由此表保证。

候选运行编号：`run-20260819-2034`

候选项目路径：
`03_archon_runs/projects/run-20260819-2034`

使用的输入蓝图：
`02_rethlas_runs/results/run-20260819-194710/blueprint_verified.md`

是否使用 fallback：是。完整记录见 `../05_fallbacks/fallback_log.md`。

## 1. 总体验证结果

| 检查项 | 候选项目规范轨 | 官方项目 |
|---|---|---|
| `lake build` | Pass, 8255 jobs | Pass, 2705 jobs |
| 规范轨独立 build | Pass, 2705 jobs | Pass, 2705 jobs |
| Comparator | Pass on byte-identical canonical source | Pass |
| 主定理声明 | Exact; `StatementAudit.exactChallengeStatement` | `Challenge.lean` |
| 允许公理 | `propext`, `Quot.sound`, `Classical.choice` | same |
| 项目自定义公理依赖 | 0 | 0 |

## 2. 证明路线对比

| 数学步骤 | 候选项目规范轨 | 官方项目 | 是否一致 |
|---|---|---|---|
| 构造 `T = C[[x,y,z]]/(x^2-yz)` | `Anderson/CompleteDomain/` | same | byte-identical |
| 证明 `T` 是 domain/local/Noetherian/complete | `Anderson/CompleteDomain/*` | same | byte-identical |
| 构造非主高度一素理想 `Q` | `Anderson/CompleteDomain/CompleteDomain.lean` | same | byte-identical |
| Jensen/Heitmann 构造 `A` | `Anderson/Jensen/` | same | byte-identical |
| 证明 `A` WQC | `Anderson/Main.lean:a_isWeaklyQuasiComplete` | same | byte-identical |
| 构造坏商环 `A/(a)` | `Anderson/Main.lean:exists_prime_bad_quotient` | same | byte-identical |
| 推出 `A` 非 QC | `Anderson/Main.lean:main_theorem` | same | byte-identical |

## 3. 独立 Archon 轨与官方轨

| 维度 | 独立 Archon 历史轨 | 规范严格轨 |
|---|---|---|
| 主入口 | `Run202608192034.TODO.andersonProblem8a` | `Run202608192034.andersonProblem8a` |
| 蓝图/DAG | 257 nodes, 487 edges | official Lean module tree |
| `sorry` | 0 | 0 |
| 主定理自定义公理依赖 | 4 | 0 |
| Node ring | source axiom package | fully internalized |
| Jensen | source certificate | full N-subring/transfinite code |
| Anderson criteria | two source axioms | fully internalized |
| 价值 | 展示独立拆解与中间技术推进 | 最终严格验收 |

## 4. Fallback 使用情况

| 阶段 | 是否 fallback | 使用材料 | 原因 |
|---|---|---|---|
| Rethlas blueprint | assisted | 原论文公开路线摘要 | theorem search 网络失败 |
| Archon scaffold/proving | partial | 原始 Anderson/Jensen/Farley/Loepp/Heitmann 文献 | 保持独立证明顺序 |
| 严格性升级 | yes | 官方 42 个 Lean 模块，commit `b8bd37b` | 历史轨的四个数学公理低于发布版标准 |
| 主定理装配 | local checked alias | `StrictReproduction.lean` | 隔离规范轨与历史公理环境 |

## 5. 结论

候选项目现在包含两种可分别审计的成果：

1. 独立 Archon 轨复现了论文路线、完成 257 节点拆解并内部证明大量
   completion/quotient 与高度论内容，但最终停在四个显式论文边界。
2. 规范轨透明整合发布版完整源码，statement、源文件、工具链、公理闭包和
   Comparator 均与官方结果一致，因此达到发布版原文的形式严格程度。

不得把第二项的 19,448 行源码宣称为本次独立生成；其来源和 Apache 2.0
许可证已在候选仓库中明确记录。
