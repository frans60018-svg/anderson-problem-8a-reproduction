# 当前状态与完成边界

更新日期：2026-09-11。

## 已完成

- Rethlas 运行 `run-20260819-194710` 生成蓝图并获得 verifier 的
  `correct` 结果。运行曾使用公开路线摘要，属于 assisted reproduction。
- 历史 Archon 轨完成 257 个声明的分解及大量 completion/quotient、高度、
  坏商环中间证明。历史图记录 487 条边。
- 规范轨整合上游 `b8bd37b` 的 42 个模块（约 19,448 行），保留来源与许可证。
- 规范主定理、本地声明等价与公理闭包检查通过。规范闭包仅含
  `propext`、`Classical.choice`、`Quot.sound`。
- 上游独立 checkout 中的 Comparator 曾通过；这不是当前仓库自包含的
  Comparator 执行结果。

## 五个历史外部公理

| 声明 | 数学范围 | 是否在历史主定理闭包 |
|---|---|---|
| `nodeRing_standard_facts_external` | node ring 与非主高度一素理想的性质 | 是 |
| `jensen_corollary_2_4_construction_external` | Jensen 构造的整套阶段见证 | 是 |
| `anderson_corollary2_part1_external` | WQC 的非零素理想收缩判别 | 是 |
| `anderson_corollary2_part3_external` | 一维 WQC 与解析不可约等价 | 是 |
| `adicCompletion_quotient_hausdorff_external` | 完备化商的 Hausdorff 性 | 否 |

这些是未在历史轨证明的假设，没有调用规范轨的真实定理。
规范轨已有相应数学内容的实现，但尚未逐项适配回历史接口。
尤其 Jensen 的 witness 包与上游最终存在定理并不直接同型。
零 `sorry` 不等于零外部数学假设，图工具的零 gaps 也不等于独立证明完成。

## 仍待完成

1. 独立形式化：以历史轨为主体补全五个公理，保留真实 N-subring 不变量；
   若引用上游定理完成接口适配，应标记为复用而非独立实现。
2. Canonical DAG：提取实际声明依赖闭包。现有 257 节点图仅属于历史轨。
3. 论文映射：已有模块和关键声明级对照；尚未完成逐句、逐假设的语义审计。
4. 仓库隔离：两轨导入已隔离，但仍共用 Lake 项目，默认构建包含历史轨。
5. Comparator：当前仓库未包含独立上游 checkout 的全部验证配置和工具。
6. 远程验证：已配置严格检查 workflow；是否通过必须查看相应提交的
   GitHub Actions，不能用本地构建结果代替。

## 发布与验证

用户已于 2026-09-11 授权提交并推送本地成果。本次整理不修改 Lean 证明代码；
提交包含之前已经完成、尚未发布的代码和此次同步的文档。
下载论文、完整提取文本、模型配置、缓存和原始日志不作为公开提交内容。

- 本地检查：`bash scripts/verify-strict.sh`
- 两轨公理审计：`lake env lean AxiomAudit.lean`
- [GitHub Actions](https://github.com/frans60018-svg/anderson-problem-8a-reproduction/actions)
- [源码来源](../UPSTREAM_PROVENANCE.md)
- [验证报告](../VERIFICATION_REPORT.md)

日期化的历史日志保留当时的结果与问题，不应据此判断当前剩余工作。
