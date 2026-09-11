# Anderson 问题 8(a) 的严格 Lean 复现

本仓库形式化证明 Anderson 2014 年提出的 Problem 8(a) 的否定答案：

**来源与贡献说明（2026-09-11）：** 完整规范证明来自 FrenzyMath
`Anderson-Conjecture` 提交 `b8bd37b`，本项目完成其整合、构建和审计。
本次 Rethlas/Archon 辅助复现过程与中间证明另行保留；历史轨仍有 5 个
外部公理，不能声称全部证明由本次独立生成。
文档入口见 [项目导航](docs/PROJECT_GUIDE.md)，准确的完成范围和待办见
[当前状态](docs/CURRENT_STATUS.md)。

> 存在一个 Noetherian local ring，它是 weakly quasi-complete，但不是
> quasi-complete。

规范验收入口是：

```lean
Run202608192034.andersonProblem8a
```

其完整类型为：

```lean
theorem andersonProblem8a :
    ∃ (R : Type) (_ : CommRing R) (_ : IsLocalRing R)
      (_ : IsNoetherianRing R),
      IsWeaklyQuasiComplete R ∧ ¬ IsQuasiComplete R
```

`IsWeaklyQuasiComplete` 和 `IsQuasiComplete` 直接使用
`IsLocalRing.maximalIdeal R`，所以主定理不再量化一个任意理想；这与原题和
发布版 `Challenge.lean` 的声明完全一致。

## 验收状态

截至 2026-09-11（本地验证；远程状态见 GitHub Actions）：

| 检查项 | 结果 |
|---|---:|
| 规范证明源码 | 42 个 `Anderson/` 模块，约 19,448 行 Lean |
| 规范源码中的 `sorry` / `admit` | 0 |
| 规范源码中的自定义 `axiom` / `opaque` | 0 |
| 规范主定理依赖的项目自定义公理 | 0 |
| `#print axioms` | `propext`、`Classical.choice`、`Quot.sound` |
| `lake build` | 通过，8255 jobs |
| 发布版 Comparator | 在独立上游 checkout 本地通过，详见验证报告 |
| Lean / Mathlib | `v4.29.0-rc8` |

`propext`、`Classical.choice` 和 `Quot.sound` 是 Lean/Mathlib 正常使用的逻辑
基础，不是本工程引入的数学假设。

## 两条证明轨

### 规范严格证明轨

`Anderson/` 包含从底层交换代数到最终反例的完整 Lean 证明。当前规范主定理
直接调用该证明轨的 `main_theorem`。这一轨已经内部化：

- node ring 的整性、Noetherian、局部、完备和维数性质；
- 非主高度一素理想 `Q` 的构造；
- Jensen/Heitmann 的 N-subring、A-extension、规避与超限构造；
- completion criterion、UFD 输出和 trivial generic formal fiber；
- adic completion 的 local 与 Noetherian 结构；
- Anderson/Farley 的 weak quasi-complete 素理想判别；
- 一维情形下 weak quasi-complete 与 analytic irreducibility 的等价；
- completion/quotient、going-down、高度和 UFD 主化论证；
- 最终 weakly quasi-complete 但非 quasi-complete 的反例。

### 历史 Archon 分解轨

`Run202608192034.TODO.andersonProblem8a`、`Run202608192034/Basic.lean`、
blueprint 和 257 节点 DAG 保留了本次复现早期的逐层拆解工作。这条轨内部证明
了大量 completion/quotient 和高度论中间结果，但还声明了五个显式外部事实，
其中四个进入旧主定理依赖闭包。

它现在只作为以下内容的研究记录：

- 如何从自然语言证明建立定理 DAG；
- 如何把大范围 `sorry` 拆成局部 lemma；
- 如何逐步内部化 completion/quotient 核心链条；
- 如何用 `#print axioms` 区分零 `sorry` 与零数学假设。

历史轨不是当前规范验收入口。完整区别见
[`TRUST_BOUNDARY.md`](TRUST_BOUNDARY.md)。

## 严格证明路线

### 1. 定义 quasi-completeness

[`Anderson/Basic.lean`](Anderson/Basic.lean) 按 Anderson Definition 1.1 定义：

```text
IsQuasiComplete R
IsWeaklyQuasiComplete R
```

二者使用局部环的唯一极大理想，不接受额外的任意 adic ideal 参数。

### 2. 内部证明 Anderson 判别定理

[`Anderson/QuasiCompleteRing/QuasiCompleteRing.lean`](Anderson/QuasiCompleteRing/QuasiCompleteRing.lean)
证明：

- weak quasi-completeness 等价于完备化中每个非零素理想与原环非平凡相交；
- 一维 Noetherian local domain 弱拟完备当且仅当解析不可约；
- quasi-complete 当且仅当所有真商环 weakly quasi-complete。

这些结果不再作为 Anderson Corollary 2 的外部公理调用。

### 3. 构造 complete local node

[`Anderson/CompleteDomain/`](Anderson/CompleteDomain/) 构造

```text
T = C[[x,y,z]] / (x^2 - yz),    Q = (x,y)T.
```

Lean 内部证明 `T` 是 complete Noetherian local domain，并证明 `Q` 非零、素、
高度一且非主。实现包含幂级数代入、正规形/系数计算、局部性、adic 完备性、
维数和 Nakayama 型论证。

### 4. 内部化 Jensen/Heitmann 构造

[`Anderson/Jensen/`](Anderson/Jensen/) 定义原文所需的强 `NSubring`：其字段
包括 UFD、quasi-local、基数界、极大理想收缩以及 associated-prime 高度界。

随后证明：

- 初始 N-subring；
- cardinal prime avoidance 和 transcendental adjoining；
- A-extension 中的素元保持；
- finitely generated ideals 的 close-up；
- well-order/transfinite successor 与 limit 阶段；
- 最终并环的 UFD、Noetherian 和 completion 性质；
- completion 为 `T` 且 generic formal fiber 为零素理想。

这替代了历史轨中的 `jensen_corollary_2_4_construction_external`。

### 5. 得到 weakly quasi-complete 源环

Jensen 构造给出 local UFD `A`，其极大理想完备化同构于 `T`，generic formal
fiber 只有零素理想。由已经内部证明的 Anderson/Farley 判别，`A` weakly
quasi-complete。

### 6. 构造坏商环

在 [`Anderson/Main.lean`](Anderson/Main.lean) 中令 `q = Q ∩ A`。Lean 证明：

- `q` 非零且高度一；
- UFD 性给出 `q=(a)`，其中 `a` 是素元；
- `aT` 严格包含于 `Q`，因此 `aT` 不是素理想；
- `T/aT` 不是整环；
- `A/aA` 是一维 Noetherian local domain，且其完备化不是整环；
- 因而 `A/aA` 不是 weakly quasi-complete。

### 7. 否定 quasi-completeness

若 `A` quasi-complete，则每个真商环都 weakly quasi-complete，这与
`A/aA` 的结论矛盾。因此 `A` weakly quasi-complete 但不 quasi-complete。

## 目录结构

| 路径 | 内容 |
|---|---|
| `Anderson/` | 规范的零项目公理完整证明 |
| `Anderson/Main.lean` | 严格证明的最终装配 `main_theorem` |
| `StrictReproduction.lean` | 与历史轨导入隔离的规范入口及主定理别名 |
| `Run202608192034.lean` | 历史 Archon 主证明轨 |
| `Run202608192034/Basic.lean` | 历史轨的基础与 completion 开发 |
| `AxiomAudit.lean` | 同时审计规范轨和历史轨的真实公理闭包 |
| `StatementAudit.lean` | 检查规范主定理与原题声明完全同型 |
| `TRUST_BOUNDARY.md` | 两条证明轨的信任边界 |
| `UPSTREAM_PROVENANCE.md` | 完整源码来源、提交和许可证信息 |
| `VERIFICATION_REPORT.md` | 本地构建、公理、声明和 Comparator 验收记录 |
| `LICENSES/` | 引入源码的 Apache 2.0 许可证 |
| `blueprint/`、`.leandag/` | 历史 Archon 轨的蓝图和依赖图 |

## 构建与审计

```bash
lake build
lake env lean StatementAudit.lean
lake env lean AxiomAudit.lean
```

规范源码 hole/axiom 扫描：

```bash
rg -n '^[[:space:]]*(axiom|opaque)[[:space:]]|^[[:space:]]*sorry[[:space:]]*$|by[[:space:]]+sorry|admit' \
  Anderson Anderson.lean StrictReproduction.lean
```

该命令应无输出。`AxiomAudit.lean` 的前两项应输出：

```text
'Run202608192034.andersonProblem8a' depends on axioms:
[propext, Classical.choice, Quot.sound]

'main_theorem' depends on axioms:
[propext, Classical.choice, Quot.sound]
```

## 来源与许可证

规范证明源码来自 FrenzyMath 的公开 `Anderson-Conjecture`，固定到提交
`b8bd37b`，按 Apache License 2.0 使用。没有引入上游带 `sorry` 的挑战模板。
详见 [`UPSTREAM_PROVENANCE.md`](UPSTREAM_PROVENANCE.md) 和许可证副本。
发布版 Comparator 的本地重放结果见
 [`VERIFICATION_REPORT.md`](VERIFICATION_REPORT.md)。

## 主要文献

1. Daniel D. Anderson, “Quasi-complete Semilocal Rings and Modules,”
   *Commutative Algebra*, Springer, 2014, pp. 25-37,
   DOI `10.1007/978-1-4939-0925-4_2`。
2. Jonathan David Farley, “Quasi-completeness and localizations of polynomial
   domains,” *Bulletin of the Korean Mathematical Society* 53(6), 2016,
   pp. 1613-1615, DOI `10.4134/BKMS.b140895`。
3. David Jensen, “Completions of UFDs with Semi-Local Formal Fibers,”
   *Communications in Algebra* 34(1), 2006, pp. 347-360,
   DOI `10.1080/00927870500346321`。
4. Raymond C. Heitmann, “Characterization of completions of unique
   factorization domains,” *Transactions of the AMS* 337(1), 1993,
   pp. 379-387, DOI `10.1090/S0002-9947-1993-1102888-9`。
5. Susan Loepp, “Constructing Local Generic Formal Fibers,” *Journal of
   Algebra* 187(1), 1997, pp. 16-38, DOI `10.1006/jabr.1997.6768`。

## 完成口径

规范主定理现已达到发布版原文的形式化严格程度：声明一致、无 `sorry`、无
项目自定义公理，并由相同 Lean/Mathlib 工具链完整构建。历史 Archon 轨仍有
显式外部边界，但它不进入规范主定理的依赖闭包。
