# 严格复现源码来源

## 规范证明轨

本仓库的规范主定理是：

```lean
Run202608192034.andersonProblem8a
```

它复用仓库内 `Anderson/` 目录中的完整证明源码。该源码来自：

- 项目：FrenzyMath, `Anderson-Conjecture`
- 仓库：`https://github.com/frenzymath/Anderson-Conjecture`
- 上游提交：`b8bd37b`（Initial commit）
- 许可证：Apache License 2.0
- 本地许可证副本：`LICENSES/Anderson-Conjecture-Apache-2.0.txt`
- Lean / Mathlib：`v4.29.0-rc8`

没有复制上游带 `sorry` 的题目模板 `Challenge.lean`，只整合了实际证明模块
`Anderson.lean` 与 `Anderson/`。

## 为什么整合这部分源码

早期 Archon 轨把尚未内部化的交换代数内容明确声明为五个外部事实，其中四个
进入旧主定理的依赖闭包。这种实现可以审计，但严格程度低于论文发布的完整
Lean 形式化。上游项目已经在相同工具链下内部证明了这些内容，包括：

- node ring 的整性、局部性、完备性、Noetherian 性和维数性质；
- Jensen 的 N-subring、A-extension、基数规避和超限并构造；
- Heitmann completion criterion 与 UFD 输出；
- adic completion 的 Noetherian / local 结构；
- Anderson/Farley 的 weak quasi-complete 判别和一维解析不可约判别；
- 最终反例的构造。

因此规范主定理现在没有项目自定义公理，并且 `IsQuasiComplete`、
`IsWeaklyQuasiComplete` 直接以内建的局部环极大理想定义，和原题声明一致。

## 历史 Archon 轨

`Run202608192034.TODO.andersonProblem8a` 及其 257 节点 blueprint 仍保留，作为
独立复现过程、定理拆解和中间技术工作的记录。它不是规范验收入口，也不应再
被描述为最终严格证明。

## 可重复审计

```bash
lake build
lake env lean AxiomAudit.lean
rg -n '^[[:space:]]*(axiom|opaque)[[:space:]]|^[[:space:]]*sorry[[:space:]]*$|by[[:space:]]+sorry|admit' \
  Anderson Anderson.lean StrictReproduction.lean
```

规范主定理的 `#print axioms` 输出应只包含 Lean/Mathlib 的逻辑基础，不包含
任何本项目声明的外部公理。
