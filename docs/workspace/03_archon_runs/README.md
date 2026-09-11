# Archon Runs

本目录记录从 Rethlas 蓝图到 Lean 证明的 Archon 阶段。

## 目标流程

```text
blueprint.md
→ Archon project init
→ DAG / theorem skeleton
→ proof loop
→ polish
→ lake build
→ statement / axiom audit
→ Comparator
```

## 已完成运行

运行编号：`run-20260819-2034`

项目：

```text
projects/run-20260819-2034/
```

### 独立 Archon 历史轨

- 257 个 blueprint/Lean 声明；
- 487 条依赖边；
- 0 gaps；
- 0 isolated nodes；
- 0 actual `sorry`；
- full historical module build passes；
- 旧主定理仍依赖四个显式 source boundaries。

该轨内部完成了 completion/quotient、kernel、维数、高度、UFD
principalization、坏商环等主要中间链条。它记录真实的自动形式化推进过程，
但不再作为最终严格验收入口。

### 规范严格轨

为达到发布版原文的严格程度，项目现在另有：

```text
Anderson/                  42 个完整证明模块
StrictReproduction.lean   独立规范入口
StatementAudit.lean       challenge 定义和 statement 一致性
StrictAxiomAudit.lean     canonical 公理闭包
scripts/verify-strict.sh  CI/本地回归门
```

规范定理 `Run202608192034.andersonProblem8a`：

- 直接使用局部环极大理想定义；
- 0 `sorry` / `admit`；
- 0 项目自定义公理依赖；
- only `propext`, `Classical.choice`, `Quot.sound`；
- canonical standalone build: 2705 jobs passed；
- full workspace build: 8255 jobs passed；
- Comparator: Lean default kernel accepted the solution。

规范源码来自发布项目提交 `b8bd37b`，Apache 2.0，整合范围和独立性影响已在
`../05_fallbacks/fallback_log.md` 与项目
`UPSTREAM_PROVENANCE.md` 中明确记录。

## 验收

```bash
cd projects/run-20260819-2034
bash scripts/verify-strict.sh
```

权威状态文件：

- `projects/run-20260819-2034/README.md`；
- `projects/run-20260819-2034/TRUST_BOUNDARY.md`；
- `projects/run-20260819-2034/VERIFICATION_REPORT.md`；
- `projects/run-20260819-2034/.archon/PROGRESS.md`。

## 完成状态

上游整合轨已通过本地严格检查，历史轨仍有五个公理。规范 DAG、逐句映射与
自包含 Comparator 尚待完成。用户已于 2026-09-11 授权 GitHub 发布；
远程 CI 结果应按发布提交检查。
