# Anderson 问题 8(a) 的 Lean/Archon 复现工作区

这个仓库记录的是对 Anderson 关于 quasi-complete / weakly quasi-complete
局部环问题的形式化复现工作。目标是沿着原论文及相关文献中的路线，在
Lean + Mathlib 中复现如下结论：

> 存在一个 Noetherian local ring，它是 weakly quasi-complete，但不是
> quasi-complete。

目前这个项目还没有完成全部形式化证明，但已经建立了从原论文证明路线到
Lean 定理骨架的完整工作区，并且已经推进了一部分中间证明节点。

## 仓库内容

- `Run202608192034/Basic.lean`  
  基础定义和判别准则，包括 quasi-complete、weakly quasi-complete、
  generic formal fiber、analytic irreducibility，以及后续证明需要使用的
  completion-prime 判别准则。

- `Run202608192034.lean`  
  主证明骨架，按照原论文思路从显式的 complete local node ring 出发，
  经过 Jensen 的 N-subring 构造，再进入 bad quotient，最后推出 Anderson
  问题 8(a) 的反例。

- `blueprint/src/chapters/`  
  Archon blueprint。这里保存的是自然语言层面的证明结构，每个节点都和
  Lean 中的声明对齐。

- `.archon/PROGRESS.md` 和 `.archon/STRATEGY.md`  
  当前进度、剩余问题和下一步策略。

- `.archon/REMAINING_SORRY_BREAKDOWN.md`  
  当前 5 个 `sorry` 的细分 lemma 清单，包括对应的原论文/blueprint 句子、
  需要的 Mathlib API 类型，以及当前是否能直接证明。

- `references/`  
  文献索引和资料完整性说明。论文 PDF 和提取出的全文文本只保存在本地工作区，
  没有上传到 GitHub，以避免仓库过大和版权问题。

- `lakefile.toml`、`lake-manifest.json`、`lean-toolchain`  
  Lean/Mathlib 环境配置。

## 当前进度

最近一次本地验证结果如下：

- blueprint 节点数：74
- 依赖边数：154
- 未匹配 Lean 声明：0
- blueprint gaps：0
- isolated nodes：0
- 当前仍有 `sorry` 的声明：5 个
- 已完成 Lean 代码量：38,025 characters
- `leandag` 估计剩余有限工作量：1,046 characters
- `lake build` 通过
- `leandag build --html` 通过
- `archon blueprint-doctor --json` 通过

也就是说，目前的状态是：证明路线、blueprint、Lean 声明和依赖图已经对齐；
整个 Lean 项目可以构建；当前还有 5 个源级数学节点仍然需要继续形式化。

## 已完成的主要工作

当前工作已经完成了以下几部分：

1. 整理原论文路线，并把证明拆成 74 个 blueprint 节点。
2. 下载并核对所需文献，包括 Anderson、Farley、Jensen、Loepp、Heitmann。
3. 建立 Lean 项目，并把所有 blueprint 节点映射到 Lean 声明。
4. 将 quasi-complete 和 weakly quasi-complete 写成下降理想链的 Lean 定义。
5. 将 generic formal fiber 表达为 completion 中素理想对原环的零收缩条件。
6. 建立 node ring
   `C[[x,y,z]] / (x^2 - yz)` 和其中的 distinguished prime candidate。
7. 将最终结论改成真实的存在性命题，而不是 `True` 型占位命题。
8. 消除了若干纯连接型 `sorry`，包括从 bad quotient 推出最终非
   quasi-complete 的步骤。
9. 前一轮把 `sorry` 从 18 个减少到 10 个，主要推进 Jensen 第二层构造接口。
10. 本轮把 completion / formal fiber 的 3 个判别准则从裸 `sorry` 改成显式
    source criterion 接口，并把这些准则作为数据沿主证明链传递。
11. 本轮继续把 5 个 node ring 局部代数事实收束到 `completeDomainChoice`
    这个源事实包中，其余 node ring 声明从该事实包投影得到。
12. 已加强 `primeGenerator` 和 `badQuotient` 的数据包，使其保留 completion map
    `ι`、`q = comap ι nodePrime`、`q = span {a}` 等后续证明需要的数据。
13. `extendedPrincipal_not_prime` 已写成 Lean 证明：从
    `q = span {a}` 推出 `map ι q = span {ι a}`，证明该扩张主理想非零且
    包含于 `nodePrime`，再用 Krull 主理想定理/高度比较推出若它为素理想
    则等于 `nodePrime`，从而和 `nodePrime` 非主性矛盾。
14. 已将 bad quotient completion 步骤拆成三个更细的 blueprint/Lean 节点：
    `extendedPrincipal_not_prime_of_generator_data`、
    `quotient_not_domain_of_not_prime` 和 `badQuotient_completion_source`。
    其中商环非整环的 Mathlib 桥已经证明，公开的
    `badQuotient_completion_not_domain` 现在从 completion source package
    和扩张主理想非素性推出。
15. 进一步把 bad quotient 的剩余源缺口前移到
    `badQuotient_criteria_source`：`badQuotient_completion_source` 现在由
    Lean 通过选择 completion target 为
    `nodeRing / Ideal.span {ι a}` 和恒等同构推出。
16. 最新一轮把 bad quotient 的剩余源缺口拆成结构化数据包
    `BadQuotientSourceData`、两个判别准则字段
    `QuasiCriterion` / `DimensionCriterion`，以及无 `sorry` 的展开引理
    `badQuotient_criteria_source`。真正剩下的 bad quotient 源洞现在是
    `badQuotient_structured_criteria_source`。
17. 继续把 bad quotient 源洞向原论文上游拆分：新增
    `JensenCompletionWitness` 表达 \(\widehat A\cong T\)，新增
    `QuotientCompletionWitness` 表达 \(\widehat{A/q}\cong T/aT\)，并证明
    `QuotientCompletionWitness.dimensionCriterion` 可把解析不可约判别准则
    沿环等价转移到 `nodeRing / Ideal.span {ι a}`。现在真正剩下的
    bad quotient 源洞是 `badQuotient_structured_source`。
18. 最新一轮补强 `BadQuotientSourceData`：它现在同时保存
    `counterexampleRing` 见证和非零素理想收缩非零性质，并新增两个无
    `sorry` 的投影定理
    `BadQuotientSourceData.to_contractedPrime` 与
    `BadQuotientSourceData.to_primeGenerator`。这使剩余 source package
    不只服务于最终 quotient，也能回推出原论文中间的 contracted prime 和
    prime generator 节点。
19. 最新一轮按照原论文顺序把 `badQuotient_structured_source` 拆成四个
    source 入口：`badQuotient_sourceData_from_jensen`、
    `jensenCompletionWitness_source`、`quotientCompletionWitness_source` 和
    `badQuotient_quasiCriterion_source`。因此 `sorry` 数量从 2 个变为
    5 个，但 `badQuotient_structured_source` 本身现在是组合证明，不再是一个
    扁平大洞。
20. 最新一轮把 `badQuotient_sourceData_from_jensen` 证明掉，并新增更上游的
    `primeGenerator_source`。这一步把 bad quotient 数据的来源移回原论文中
    “\(q=Q\cap A\) 是高度一素理想，因 \(A\) 是 UFD 所以 \(q=aA\)”这一句。
21. 之前继续把 `primeGenerator_source` 拆成四个源输入：
    `jensenSpecialCase_isUFD_source`、weak criterion、contracted-prime height
    和 `heightOnePrime_principal_of_ufd_source`。经过后续整合，weak criterion
    和 completion-map going-down 都已经统一收束到 `JensenCompletionWitness`。
22. 本轮进一步证明了 `heightOnePrime_principal_of_ufd_source`：在 UFD 中，
    非零高度一素理想包含一个素元 \(p\)，而 \((p)\subseteq q\) 的严格包含
    会违反两个高度一素理想之间的 `primeHeight` 严格单调性。因此这个节点
    不再是 source 接口，而是实际 Lean 证明。
23. 本轮继续拆开 `contractedPrime_height_one_source`：已证明
    `nonzeroPrime_height_ge_one_source`，即整环中非零理想高度至少为 1；
    真正剩下的高度问题被压缩到
    `contractedPrime_height_le_one_source`，对应原论文中 completion map
    faithfully flat 和 going-down 给出的高度上界。
24. 之前进一步证明了通用 going-down 高度比较
    `liesOver_height_le_of_hasGoingDown_source`，并把
    `contractedPrime_height_le_one_source` 本身改成组合证明；后续又把
    completion-map going-down 从独立 source hole 改成
    `JensenCompletionWitness` 的 checked consequence。
25. 最新一轮继续缩小 `completionMap_hasGoingDown_source`：新增并证明
    `adicCompletion_hasGoingDown_of_isNoetherian`。Lean 现在可以直接从
    Mathlib 的 Noetherian adic completion 平坦性和 flat algebra going-down
    实例推出标准 adic completion map 满足 going-down。
26. 最新一轮进一步证明
    `adicCompletion_equiv_hasGoingDown_of_isNoetherian`：如果有
    `AdicCompletion 𝔪 A ≃+* T`，那么通过这个等价传输得到的
    `A -> T` 也满足 going-down。证明使用完成映射的 flatness、双射环同态的
    flatness，以及 flatness 对复合的稳定性。现在剩下的不是一般平坦性，
    而是把 Jensen 选出的 `ι : A -> nodeRing` 严格识别为
    `AdicCompletion 𝔪 A ≃+* nodeRing` 下的标准完成映射。
27. 最新一轮把 `JensenCompletionWitness` 改成直接使用 Mathlib 的
    `AdicCompletion 𝔪 A`，并让它同时保存
    `AdicCompletion 𝔪 A ≃+* nodeRing`、映射兼容等式
    `ι = completionEquiv.toRingHom.comp (algebraMap A (AdicCompletion 𝔪 A))`
    和 weak-completeness criterion。于是
    `counterexampleRing_weakCriterion_source` 现在只是从 witness 投影，
    `completionMap_hasGoingDown_source` 现在由映射兼容等式加上已经证明的
    going-down transport lemma 推出。`sorry` 数量从 7 个降到 5 个。

## 最近消除的 8 个 `sorry`

最近一轮工作主要完成的是 Jensen 构造中的第二层接口。具体包括：

- `cardinal_prime_avoidance`
- `jensen_residueField_uncountable`
- `initialNSubring`
- `nSubring_prime_extension`
- `nSubring_ideal_extension`
- `jensenUnion_isUFD`
- `jensen_completion_criterion`
- `jensen_semilocal_genericFiber`

需要说明的是，这些节点目前还不是对论文中最深构造的完整形式化。当前做法是：
把论文中需要的关键假设或见证显式写入 Lean 声明，然后让 Lean 检查这些见证确实
能推出后续需要的结论。这样可以避免保留过强甚至不成立的占位陈述，也让后续
真正补全 Jensen 构造时有清晰接口。

## 本轮消除的 3 个 completion / formal fiber `sorry`

本轮处理的是基础文件中的三个判别准则接口：

- `quasiComplete_iff_all_quotients_weak`
- `weaklyQuasiComplete_iff_completion_primes`
- `dimensionOne_weaklyQuasiComplete_iff`

原来的 Lean 声明对任意 completion target 都成立，形式上过强。现在的做法是：
把 Farley / Anderson 中使用的判别标准作为显式 source criterion 假设传入，
定理本身负责把该 source criterion 变成后续证明可以调用的 Lean 接口。
这消除了 3 个 `sorry`，同时保留了后续真正形式化这些判别准则的位置。

## 本轮推进的 node ring 部分

本轮处理的是显式 node ring
`C[[x,y,z]] / (x^2 - yz)` 相关的 5 个分散 `sorry`：

- `nodeRing_isDomain`
- `node_complete_cm_dim`
- `node_cardinality`
- `nodePrime_prime_height`
- `nodePrime_not_principal`

现在这些节点都不再各自保留裸 `sorry`，而是从 `completeDomainChoice` 投影得到。
`completeDomainChoice` 被加强为一个包含 node ring 标准事实的 source package：
domain、Noetherian local、维数为 2、基数为 `|C|`、`nodePrime` 是非零高度一素理想，
并且 `nodePrime` 非主。

这一步把 node ring 缺口从 5 个分散证明压缩成 1 个明确的源事实包。后续如果要
完全贴合原论文，需要继续把这个 source package 展开成实际证明：构造到
`C[[u,v]]` 的嵌入、证明 kernel 正好是 `(x^2-yz)`，再形式化维数、基数、高度和
Nakayama 非主性论证。

## 本轮消除的 extended principal `sorry`

本轮继续完成了 `extendedPrincipal_not_prime`。证明内容与原论文该段一致：

- 由 `q = span {a}` 和 `q = comap ι nodePrime` 得到
  `Ideal.map ι q = Ideal.span {ι a}` 以及 `Ideal.span {ι a} ≤ nodePrime`。
- 由 `comap ι ⊥ = ⊥` 得到 `ι` 单射，所以扩张主理想非零。
- 如果 `Ideal.span {ι a}` 是素理想，Mathlib 的
  `Ideal.height_le_spanRank_toENat` 给出其高度至多为 1。
- 由于 `nodeRing` 是整环，非零素理想高度至少为 1；于是该主素理想高度为 1。
- 它包含在同样高度为 1 的 `nodePrime` 中，严格包含会违反
  `Ideal.primeHeight_strict_mono`，所以二者相等，矛盾于
  `nodePrime_not_principal`。

这是真正消除的一个实质性 Lean `sorry`，不是改成新的裸接口。

## 剩余的主要数学工作

当前 5 个 `sorry` 主要集中在三类问题：

1. node ring 源事实包  
   需要完整形式化 `C[[x,y,z]] / (x^2 - yz)` 的 domain、Noetherian local、
   二维、基数、`Q = (x,y)` 的高度一素性和非主性。

2. prime generator 的 Jensen/UFD 来源  
   现在还剩两个源级入口：
   `jensenSpecialCase_isUFD_source` 和 `jensenCompletionWitness_source`。
   其中“高度一素理想在 UFD 中主”、“非零理想高度至少为 1”、
   “going-down + lies-over 推高度上界”、标准 adic completion 的
   going-down、以及沿 ring equivalence 传输 going-down，均已由 Lean 证明。
   Farley weak criterion 和 selected completion map 的 going-down 现在都集中
   在 `JensenCompletionWitness` 这个统一接口里。

3. bad quotient 的 completion 不是 domain  
   这是最后构造反例的关键步骤。现在“利用扩张后的主理想不是素理想来证明
   completion 非整环”的后半段已经完成；剩下的是两个源级入口：
   `quotientCompletionWitness_source` 和 `badQuotient_quasiCriterion_source`。

当前结构已经和原论文顺序更一致：先由 Jensen/UFD 给出 \(A,q,a\) 数据，再用
统一的 `JensenCompletionWitness` 记录 \(\widehat A\cong T\)、映射兼容性和
Farley criterion，随后记录 completion commutes with quotient 给出的
\(\widehat{A/q}\cong T/aT\)，最后才把判别准则展开给后续主证明使用。

如果要继续提高对原论文的贴合度，completion / formal fiber 的三个 source
criterion 仍需要在后续阶段从引用文献中完整形式化，而不是长期停留为接口假设。

更细的剩余任务拆分见 `.archon/REMAINING_SORRY_BREAKDOWN.md`。

## 如何本地验证

在项目根目录运行：

```bash
lake build
../../../tools/Archon/.venv/bin/leandag build --html
../../../tools/Archon/.venv/bin/leandag --plain stats
../../../tools/Archon/.venv/bin/leandag --plain show gaps
../../../tools/Archon/.venv/bin/leandag --plain show isolated
../../../tools/Archon/.venv/bin/archon blueprint-doctor --json
```

## 下一步计划

下一步最重要的是把当前轻量级的 `NSubring` scaffold 替换成 Jensen 原文中的完整
定义，包括：

- quasi-local UFD 结构；
- cardinality bound；
- associated primes 对子环的零收缩；
- 对 `T / tT` 的 associated primes 的高度控制。

完成这一步之后，目前已经打通的 Jensen 接口节点就可以从“见证检查型定理”
逐步加强为真正的构造定理，从而更贴近原论文的证明顺序和证明内容。
