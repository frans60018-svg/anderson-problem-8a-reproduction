# Anderson 问题完整流程复现

本工作区按照论文 `Automated Conjecture Resolution with Formal
Verification` 的顺序复现：

```text
数学问题输入
→ Rethlas 非形式化证明搜索与验证
→ Archon 形式化拆解与证明
→ Lean build
→ statement / axiom audit
→ Comparator
→ 与官方结果对比
```

截至 2026-09-11，上游规范证明本地验收通过，工作区保留辅助 Archon 历史轨
和零项目公理的规范严格轨。历史轨独立闭合及完整流程自主复现尚未完成。

## 最终结果

规范主定理位于：

```text
03_archon_runs/projects/run-20260819-2034/
  StrictReproduction.lean
  Run202608192034.andersonProblem8a
```

验收结果：

- exact challenge statement；
- 42 个完整证明模块，约 19,448 行 Lean；
- canonical `sorry` / `admit`: 0；
- canonical custom `axiom` / `opaque`: 0；
- 公理闭包只有 `propext`、`Classical.choice`、`Quot.sound`；
- canonical standalone build: 2705 jobs passed；
- full workspace build: 8255 jobs passed；
- Comparator: `Lean default kernel accepts the solution`。

## 目录结构

```text
03_full_pipeline_reproduction/
├── README.md
├── STATUS.md
├── experiment_protocol.md
├── 01_problem_input/
├── 02_rethlas_runs/
├── 03_archon_runs/
│   └── projects/run-20260819-2034/
│       ├── Anderson/                 # 规范完整证明
│       ├── StrictReproduction.lean  # 独立规范入口
│       ├── Run202608192034.lean     # 历史 Archon 轨
│       ├── StatementAudit.lean
│       ├── AxiomAudit.lean
│       ├── TRUST_BOUNDARY.md
│       └── VERIFICATION_REPORT.md
├── 04_comparison/
└── 05_fallbacks/
```

## Phase 1: 固定问题输入

`01_problem_input/anderson_problem.md` 固定 Anderson Problem 8(a) 的陈述、
定义和允许背景，不包含官方 Lean 解答。

## Phase 2: Rethlas

运行 `run-20260819-194710` 生成：

- `blueprint.md`；
- `blueprint_verified.md`；
- `verification.json`；
- 完整 generation/verification 日志。

verifier verdict 为 `correct`。由于 theorem-search 网络失败，generation
阶段读取过原自动推理论文的公开路线摘要，因此这是 assisted reproduction，
不是 blind rediscovery。详情见 fallback log。

## Phase 3: 独立 Archon 轨

Archon run `run-20260819-2034` 从 Rethlas 蓝图建立并持续细化：

- 257 个 blueprint/Lean 声明；
- 487 条依赖边；
- 0 gaps；
- 0 isolated nodes；
- 0 actual `sorry`；
- completion/quotient、kernel、height、UFD principalization 和 bad quotient
  等大量中间证明由 Lean 内部检查。

这条轨最终仍以四个显式论文/基础设施边界支撑旧主定理。它是可审计的独立
过程成果，但严格度低于发布版零项目公理证明。

## Phase 4: 规范严格轨

用户把目标提升为“严格程度与发布版原文一致”后，工作区透明整合了
FrenzyMath `Anderson-Conjecture` 提交 `b8bd37b` 的 42 个完整 Lean 模块。
源码按 Apache 2.0 使用，且与本地上游 checkout 字节一致。

规范轨内部证明：

- node ring 的 domain/local/Noetherian/complete/dimension 性质；
- 非主高度一素理想；
- adic completion 的 local 与 Noetherian 结构；
- Anderson/Farley 的两个关键判别；
- Jensen/Heitmann 的强 N-subring、规避、close-up 和超限构造；
- UFD、completion、generic formal fiber 输出；
- 坏商环以及最终反例。

规范轨不是伪装成独立生成的代码。来源、许可证和 fallback 范围均有明确记录。

## Phase 5: 验证

在候选项目根目录执行：

```bash
cd 03_archon_runs/projects/run-20260819-2034
bash scripts/verify-strict.sh
```

脚本执行 full build、独立 challenge 定义检查、canonical axiom audit 和严格
源码扫描。预期末行：

```text
Strict reproduction checks passed.
```

发布版 Comparator 也已经在 byte-identical 源码上本地重放成功。完整结果见
`VERIFICATION_REPORT.md`。

## Phase 6: 对比

`04_comparison/comparison_template.md` 已填写。结论是：

- 历史 Archon 轨体现本次独立研究和 proof engineering 过程；
- 规范轨在 theorem statement、Lean 源码、公理集合和 Comparator 结果上与
  发布版一致；
- 两者用途不同，不能混为“19,448 行均由本次独立生成”。

## 关键文档

- `STATUS.md`：全流程最终状态；
- `experiment_protocol.md`：原实验顺序和 fallback 原则；
- `05_fallbacks/fallback_log.md`：所有偏离 blind 主线的记录；
- `03_archon_runs/projects/run-20260819-2034/README.md`：规范仓库说明；
- `03_archon_runs/projects/run-20260819-2034/TRUST_BOUNDARY.md`：公理边界；
- `03_archon_runs/projects/run-20260819-2034/UPSTREAM_PROVENANCE.md`：源码许可；
- `03_archon_runs/projects/run-20260819-2034/VERIFICATION_REPORT.md`：最终验收。

## 当前剩余

用户于 2026-09-11 授权提交与推送。尚待完成的是历史五公理的独立实现、
canonical 声明级 DAG、逐句论文映射和当前仓库自包含 Comparator。
已有 Comparator 记录来自独立上游 checkout，远程 CI 以发布提交为准。
