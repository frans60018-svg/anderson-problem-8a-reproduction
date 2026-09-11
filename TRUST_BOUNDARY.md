# 形式化信任边界

## 规范结论

当前规范主定理是：

```lean
Run202608192034.andersonProblem8a
```

它与原题的类型完全一致，并直接由完整证明 `main_theorem` 得出。执行：

```bash
lake env lean AxiomAudit.lean
```

得到：

```text
'Run202608192034.andersonProblem8a' depends on axioms:
[propext, Classical.choice, Quot.sound]
'main_theorem' depends on axioms:
[propext, Classical.choice, Quot.sound]
```

因此规范主定理的依赖闭包中有：

- 0 个 `sorry` / `admit`；
- 0 个项目自定义公理；
- 0 个引用论文结果的未验证假设；
- 只有 Lean/Mathlib 常规逻辑基础。

## 与原题的声明一致性

原题把 quasi-completeness 定义为局部环唯一极大理想的幂所给出的条件。规范
定义 [`Anderson/Basic.lean`](Anderson/Basic.lean) 直接使用：

```lean
IsLocalRing.maximalIdeal R
```

规范主定理量化 `CommRing`、`IsLocalRing` 和 `IsNoetherianRing` 实例，然后
断言 `IsWeaklyQuasiComplete R ∧ ¬ IsQuasiComplete R`。它不再引入一个未声明
为极大的任意理想参数。

[`StatementAudit.lean`](StatementAudit.lean) 独立复制原题最终 proposition，
并以规范主定理作为证明，从而由 Lean 检查两者类型完全匹配。

## 已内部化的原论文输入

规范 `Anderson/` 证明轨已经替代早期的四个主结论外部边界：

| 早期边界 | 当前内部证明位置 |
|---|---|
| node ring 标准事实 | `Anderson/CompleteDomain/` |
| Jensen Corollary 2.4 构造 | `Anderson/Jensen/` |
| Anderson Corollary 2(1) | `Anderson/QuasiCompleteRing/QuasiCompleteRing.lean` |
| Anderson Corollary 2(3) | `Anderson/QuasiCompleteRing/QuasiCompleteRing.lean` |
| adic completion Noetherian/局部结构 | `Anderson/AdicNoetherian.lean`、`Anderson/AdicLocal.lean` |

严格证明也内部完成了 Heitmann/Loepp/Jensen 构造中使用的 N-subring、
A-extension、基数规避、close-up、Krull domain 和超限递归模块。

## 历史 Archon 轨

以下声明仍存在于历史轨，但不在规范主定理依赖闭包中：

1. `Run202608192034.TODO.nodeRing_standard_facts_external`；
2. `Run202608192034.TODO.jensen_corollary_2_4_construction_external`；
3. `Run202608192034.TODO.anderson_corollary2_part1_external`；
4. `Run202608192034.TODO.anderson_corollary2_part3_external`；
5. `Run202608192034.TODO.adicCompletion_quotient_hausdorff_external`。

保留它们是为了让旧 257 节点 DAG 和逐步开发记录仍可重放，不是规范证明的
数学假设。`AxiomAudit.lean` 同时打印旧主定理的闭包，以防两条证明轨被混淆。

## 源码信任与许可

规范证明源码来自 FrenzyMath `Anderson-Conjecture` 的提交 `b8bd37b`，在本仓库
中完整保存，因此构建不依赖另一个本地 checkout。源码按 Apache License 2.0
使用，具体来源和许可证见 `UPSTREAM_PROVENANCE.md` 与 `LICENSES/`。

## 验收命令

```bash
lake build
lake env lean StatementAudit.lean
lake env lean AxiomAudit.lean
rg -n '^[[:space:]]*(axiom|opaque)[[:space:]]|^[[:space:]]*sorry[[:space:]]*$|by[[:space:]]+sorry|admit' \
  Anderson Anderson.lean StrictReproduction.lean
```

前三条必须成功，最后一条必须没有匹配。任何只检查
`Run202608192034.TODO.andersonProblem8a` 的审计都只是在检查历史轨，不代表
当前规范结论。
