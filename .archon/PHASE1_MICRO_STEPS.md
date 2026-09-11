# Phase 1 Micro Steps: Bad Quotient Completion

> 历史执行记录。下文的目标和 `sorry` 数量是当时快照；阶段一现已全部关闭。
> 当前状态以 `.archon/PROGRESS.md` 和
> `.archon/REMAINING_SORRY_BREAKDOWN.md` 为准。

本文件把下一阶段的 bad quotient 工作拆成可以逐轮执行和验证的小目标。
阶段一的目标不是一次性完成所有 Jensen / node ring 深层构造，而是先关闭
bad quotient 下游的大块入口，并把 completion-quotient 与一维判别准则
拆成可以单独攻击的源级目标：

```text
Run202608192034.lean:763  quotientCompletionWitness_source
Run202608192034.lean:769  badQuotient_quasiCriterion_source
```

这两个入口对应原论文中从 \(B=A/aA\) 到
\(\widehat B \cong T/aT\)，再由 completion 非整环推出 quotient 破坏
quasi-completeness 的部分。

当前这两个入口已经变成 checked wrappers。剩余的 Basic 层 bad quotient 判别准则
已经拆成源义务；其中 fixed-power avoidance wrapper、finite-level
approximation wrapper 和 finite-level projection kernel-identification
都已经关闭。Farley 第一方向中的 completion-neighborhood Krull-intersection
入口也已经进一步拆分：原来的
`adicCompletion_neighborhood_iInf_le_prime_source` 现在是 checked wrapper，
剩余 source obligation 下沉为 quotient completion 的 Hausdorff/closed-ideal
输入。当前剩余的是：

```text
Run202608192034/Basic.lean:324  adicCompletion_quotient_hausdorff_source
Run202608192034/Basic.lean:915  weaklyQuasiComplete_badChain_to_adicCompletion_badPrime_source
Run202608192034/Basic.lean:964  dimensionOne_adicCompletion_primeContraction_iff_analyticIrreducible_source
```

## 当前可用输入

Lean 中已经有：

- `BadQuotientSourceData d`：保存 `A`、`𝔪`、`ι : A →+* nodeRing`、
  `q`、`a`、`q = Ideal.comap ι nodePrime`、`q.IsPrime`、
  `q = Ideal.span {a}` 等数据。
- `JensenCompletionWitness d.A d.𝔪 d.ι`：保存
  `AdicCompletion d.𝔪 d.A ≃+* nodeRing`、映射兼容等式和 weak criterion。
- `extendedPrincipal_not_prime_of_generator_data`：证明扩张主理想
  `Ideal.span {d.ι d.a}` 不是素理想。
- `quotient_not_domain_of_not_prime`：证明如果 `I` 不是素理想，则
  `R ⧸ I` 不是整环。
- `QuotientCompletionWitness.dimensionCriterion`：已经能把 completion target
  与 `nodeRing ⧸ Ideal.span {d.ι d.a}` 的等价转化成 dimension criterion。

Mathlib 中确认可用的相关 API：

- `AdicCompletion.map_surjective`
- `AdicCompletion.map_injective`
- `AdicCompletion.map_exact`
- `AdicCompletion.map_comp`
- `AdicCompletion.map_of`
- `AdicCompletion.congr`
- `AdicCompletion.evalₐ`
- `Ideal.quotientEquivAlgOfEq`
- `Ideal.quotientKerAlgEquivOfSurjective`
- `Ideal.quotientMap`
- `Ideal.quotientMapₐ`
- `Ideal.Quotient.mk_surjective`

## Step 1.1: 固化 quotient map 的线性 exact sequence

状态：已完成。

目标：把商映射

```lean
Ideal.Quotient.mk d.q : d.A →+* d.A ⧸ d.q
```

对应的线性映射整理出来，并证明它是满射，kernel 正好是 `d.q`。

建议 Lean lemma：

```lean
lemma quotient_mk_linear_surjective
    (d : BadQuotientSourceData) :
    Function.Surjective
      ((Ideal.Quotient.mk d.q).toMonoidWithZeroHom.toAddMonoidHom ...)
```

实际实现时不一定要使用这个精确名字，可以优先写更贴合 Mathlib 的
`LinearMap` 版本。

成功标准：

- 能把 `Ideal.Quotient.mk_surjective` 转成 `AdicCompletion.map_surjective`
  所需的线性满射输入。

当前判断：可以直接证明，但需要处理 ring hom 到 linear map 的类型转换。

完成记录：

- 已新增 `quotientLinearMap`。
- 已证明 `quotient_mk_linear_surjective`。

## Step 1.2: 用 `AdicCompletion.map_surjective` 得到完成后的商映射满射

状态：已完成。

目标：证明

```lean
AdicCompletion.map d.𝔪 (quotientLinearMap d)
```

是满射。

对应原论文句子：

> completion commutes with quotient by a finitely generated ideal.

这里先只证明“完成后的 quotient map 仍满射”，不急着识别 kernel。

建议 Lean lemma：

```lean
lemma quotient_completion_map_surjective
    (d : BadQuotientSourceData) :
    Function.Surjective
      (AdicCompletion.map d.𝔪 (quotientLinearMap d))
```

成功标准：

- 该 lemma 无 `sorry`。

当前判断：大概率可以直接证明，因为 Mathlib 已有
`AdicCompletion.map_surjective`。

完成记录：

- 已证明 `quotient_completion_map_surjective`。

## Step 1.3: 证明完成后 quotient map 的 kernel 来自 `q`

状态：已完成。

目标：识别

\[
\ker(\widehat A \to \widehat{A/q})
\]

等于 `q` 在 `AdicCompletion d.𝔪 d.A` 中的闭包 / image。

对应原论文句子：

> \(\widehat{A/aA} \cong \widehat A/a\widehat A\).

建议先写 source-interface lemma，而不是一口气展开全部 exactness：

```lean
lemma adicCompletion_quotient_kernel_source
    (d : BadQuotientSourceData) :
    RingHom.ker (completedQuotientMap d) =
      Ideal.map (algebraMap d.A (AdicCompletion d.𝔪 d.A)) d.q
```

成功标准：

- 如果能从 `AdicCompletion.map_exact` 完成，就去掉 source 后缀。
- 如果类型障碍较多，就保留这个更小的 source lemma，用它证明后续步骤。

当前判断：已解决。证明没有保留新的 source 假设：Mathlib 的
`AdicCompletion.map_exact` 给出 completed submodule range，再由 tensor
presentation 证明该 range 落入 `qAhat`。

完成记录：

- 已构造 `completedRingToQuotientCompletion : AdicCompletion d.𝔪 d.A →
  quotientAdicCompletion d`。
- 已证明 `completedRingToQuotientCompletion_ker_contains_completed_q`。
- 已构造下降映射
  `completedQuotientToQuotientCompletion : Ahat/qAhat →
  quotientAdicCompletion d`。
- 已新增 `CompletedQuotientMapSourceFacts`，把剩余 exactness 输入拆为
  `completedRing_surjective` 和 `completedRing_ker_le_completed_q` 两个字段。
- 已建立 `AdicCompletion d.𝔪 (d.A ⧸ d.q)` 与
  `quotientAdicCompletion d` 的 comparison equivalence。
- 已证明该 comparison 与 `completedRingToQuotientCompletion` 相容。
- 已由 `AdicCompletion.map_surjective` 和 comparison surjectivity 证明
  `completedRingToQuotientCompletion_surjective`。
- 已用 `AdicCompletion.map_exact` 证明 `quotient_completion_module_exact`。
- 已证明 `completedRingToQuotientCompletion_ker_le_completedSubmoduleRange`：
  kernel 已落入完成后 `q` 子模块在 `Ahat` 中的 range。
- 已证明 `completedIdealTensorImage_le_completed_q`：
  \(\widehat A\otimes_A q\to\widehat A\) 的像落入扩张理想 `qAhat`。
- 已证明 `completedSubmoduleRange_le_completed_q`：
  用有限生成模的 completion tensor 表示和自然性，把 completed submodule
  range 放进 `qAhat`。
- 已证明 `completedRingToQuotientCompletion_ker_le_completed_q_source`。
- 已证明
  `completedRingToQuotientCompletion_ker_eq_completed_q_source`。
- 已证明 `completedQuotientToQuotientCompletion_injective`。

## Step 1.4: 构造
`AdicCompletion (map mk 𝔪) (A ⧸ q) ≃+* AdicCompletion 𝔪 A ⧸ map q`

状态：已完成。外层等价构造、底层 descended map 的双射、父映射满射和 kernel
等式都已经完成。

目标：从 Step 1.2 的满射和 Step 1.3 的 kernel 等式构造商环等价。

建议 Lean lemma：

```lean
noncomputable def quotientCompletionEquivAdic_source
    (d : BadQuotientSourceData) :
    AdicCompletion (Ideal.map (Ideal.Quotient.mk d.q) d.𝔪) (d.A ⧸ d.q)
      ≃+*
    (AdicCompletion d.𝔪 d.A ⧸
      Ideal.map (algebraMap d.A (AdicCompletion d.𝔪 d.A)) d.q)
```

成功标准：

- 产生真正的 `RingEquiv`，而不只是命题形式。

当前判断：已解决。核心 descended ring hom 已经证明双射，并已包装成
`quotientCompletionEquiv_source`。

完成记录：

- 已新增 `quotientCompletionEquiv_source`，它用
  `RingEquiv.ofBijective` 从
  `completedQuotientToQuotientCompletion_bijective_source` 得到
  \(\widehat{A/q}\cong\widehat A/q\widehat A\)。
- 已证明 `completedQuotientToQuotientCompletion_surjective`：
  从父映射满射取代表元，再投到 \(\widehat A/q\widehat A\)。
- 已证明 `completedQuotientToQuotientCompletion_injective`：
  用 `RingHom.lift_injective_of_ker_le_ideal` 和 kernel 反包含。
- 已证明 `completedQuotientToQuotientCompletion_bijective_source`：
  由上述单射和满射合并。

## Step 1.5: 把 `q = span {a}` 传到 completion

状态：已完成。

目标：证明 completion 中的 `q` image 等于 `a` 的 image 生成的主理想：

```lean
Ideal.map (algebraMap d.A (AdicCompletion d.𝔪 d.A)) d.q =
  Ideal.span ({algebraMap d.A (AdicCompletion d.𝔪 d.A) d.a} : Set _)
```

对应原论文句子：

> \(q=aA\), hence \(q\widehat A=a\widehat A\).

建议 Lean lemma：

```lean
lemma completed_q_eq_span_a
    (d : BadQuotientSourceData) :
    Ideal.map (algebraMap d.A (AdicCompletion d.𝔪 d.A)) d.q =
      Ideal.span
        ({algebraMap d.A (AdicCompletion d.𝔪 d.A) d.a} : Set _)
```

成功标准：

- 应该由 `d.hqPrincipal`、`Ideal.map_span`、`Set.image_singleton` 直接证明。

当前判断：可以直接证明。

完成记录：

- 已证明 `completed_q_eq_span_a`。

## Step 1.6: 沿 `w.completionEquiv` 把 quotient target 改成 `nodeRing / aT`

状态：已完成其中不依赖 Step 1.3/1.4 的部分。

目标：构造

\[
\widehat A / a\widehat A \cong T/aT.
\]

其中 \(T=nodeRing\)，\(aT\) 在 Lean 中是：

```lean
Ideal.span ({d.ι d.a} : Set nodeRing)
```

关键输入：

- `w.completionEquiv`
- `w.map_compatible`
- Step 1.5 的 completed `q = span {a}`

建议 Lean lemma：

```lean
noncomputable def completedQuotientTargetEquivNode
    (d : BadQuotientSourceData)
    (w : JensenCompletionWitness d.A d.𝔪 d.ι) :
    (AdicCompletion d.𝔪 d.A ⧸
      Ideal.map (algebraMap d.A (AdicCompletion d.𝔪 d.A)) d.q)
      ≃+*
    (nodeRing ⧸ Ideal.span ({d.ι d.a} : Set nodeRing))
```

成功标准：

- 能把 quotient ideal 在等价下的 image 化简到 `Ideal.span {d.ι d.a}`。

当前判断：可实现，但需要 quotient-by-equivalent-ideal 的 API。
如果 Mathlib API 不顺，应先写更小 lemma：

```lean
lemma completionEquiv_maps_completed_q
```

证明 ideal image 的等式，再用 quotient equivalence。

完成记录：

- 已证明 `completionEquiv_maps_completed_q`。
- 已构造 `completedQuotientTargetEquivNode`：
  \[
  \widehat A/q\widehat A \cong T/aT.
  \]

尚未完成：

- 还没有把 `\widehat{A/q}` 形式化识别为 `\widehat A/q\widehat A`。
  这正是 Step 1.3/1.4 的内容。

## Step 1.7: 完成 `quotientCompletionWitness_source`

状态：已完成为组合证明；一个更精确的 source criterion 仍待证明。

目标：将前面两个等价复合，填入：

```lean
QuotientCompletionWitness d
```

建议实现：

```lean
noncomputable def quotientCompletionWitness_source
    (d : BadQuotientSourceData)
    (w : JensenCompletionWitness d.A d.𝔪 d.ι) :
    QuotientCompletionWitness d := by
  refine
    { Bhat :=
        AdicCompletion (Ideal.map (Ideal.Quotient.mk d.q) d.𝔪) (d.A ⧸ d.q)
      instBhat := inferInstance
      quotientCompletionEquiv := ...
      analyticCriterionOnBhat := ... }
```

`analyticCriterionOnBhat` 可以先来自一个更小的 source criterion：

```lean
lemma quotient_analyticCriterionOnAdicCompletion_source
```

对应原论文 / Farley 使用的一维判别标准。

成功标准：

- `quotientCompletionWitness_source` 本身不再是裸 `sorry`。
- 如果还需要 source criterion，`sorry` 会下沉到更精确的 lemma。

当前判断：可以作为阶段一的主要交付点。

完成记录：

- `quotientCompletionWitness_source` 本身已经不再是 `sorry`。
- 它现在选取的 completion target 是
  `AdicCompletion d.𝔪 d.A ⧸ Ideal.map (algebraMap d.A (AdicCompletion d.𝔪 d.A)) d.q`。
- 剩余 source hole 已下沉为两个更精确的目标：
  `completedQuotientToQuotientCompletion_bijective_source` 和
  `quotient_dimensionOneCriterionOnQuotientCompletion_source`；原来的
  `quotient_analyticCriterionOnCompletedQuotient_source` 现在只是通过这个
  bridge 传递 `IsDomain` 的 checked theorem。

## Step 1.8: 完成 `badQuotient_quasiCriterion_source`

状态：已完成。

目标：证明：

```lean
d.QuasiCriterion
```

展开后是：

```lean
QuasiComplete d.A d.𝔪 ↔
  ∀ J : Ideal d.A,
    WeaklyQuasiComplete (d.A ⧸ J)
      (Ideal.map (Ideal.Quotient.mk J) d.𝔪)
```

对应原论文句子：

> A local ring is quasi-complete iff all its quotient rings are weakly
> quasi-complete.

当前项目中 `Run202608192034/Basic.lean` 已有：

```lean
quasiComplete_iff_all_quotients_weak
```

它现在已经是直接从 `QuasiComplete` / `WeaklyQuasiComplete` 定义证明的
一般性定理，不再需要额外 source criterion。

成功标准：

- `badQuotient_quasiCriterion_source` 不再是裸 `sorry`。
- 基础判别标准本身无 source hypothesis。

当前判断：已实现。

完成记录：

- `badQuotient_quasiCriterion_source` 本身已经不再是 `sorry`。
- `all_quotients_weak_criterion_source` 也已经不再是 `sorry`，它现在只是
  `quasiComplete_iff_all_quotients_weak` 的专门化。
- `quasiComplete_iff_all_quotients_weak` 已在 `Basic.lean` 中直接证明：
  正向把 quotient 中零交下降链拉回原环，反向取
  \(J=\bigcap I_n\) 并在 \(R/J\) 中应用 weak quasi-completeness。

## 建议执行顺序

1. 先做 Step 1.5，因为它最容易，能快速确认 quotient ideal 记号是否顺畅。
2. 做 Step 1.2，确认 `AdicCompletion.map_surjective` 的类型路线。
3. 做 Step 1.3，把 kernel 等式作为核心难点拆出来。
4. 做 Step 1.4，获得 `A/q` completion 与 `Ahat/qAhat` 的等价。
5. 做 Step 1.6，沿 `w.completionEquiv` 转到 `nodeRing/aT`。
6. 做 Step 1.7，关闭 `quotientCompletionWitness_source` 或把它下沉成更精确的
   criterion lemma。
7. 做 Step 1.8，关闭 `badQuotient_quasiCriterion_source`。
8. 进入第二步：先证明 `A/q` 的 Noetherian/domain/local/dim-one 基础事实，
   再专门攻击一维 analytic irreducibility 判别准则。
9. 跑 `lake build`，然后更新 README、PROGRESS 和剩余 sorry 文档。

## 阶段一完成标准

最低完成标准：

```text
quotientCompletionWitness_source      不再是裸 source hole        已完成
badQuotient_quasiCriterion_source     不再是裸 source hole        已完成
lake build                            通过                       已完成
.archon/REMAINING_SORRY_BREAKDOWN.md  同步更新                   已完成
```

理想完成标准：

```text
阶段一新增的所有桥接 lemma 均无 sorry
总 sorry 数从 5 降到 3
bad quotient 下游证明链完全闭合
剩余 sorry 只集中在 completeDomainChoice、jensenCompletionWitness_source、
jensenSpecialCase_isUFD_source
```

当前实际状态：

- 总 `sorry` 数为 6。其中 3 个在顶层 Jensen/source 构造：
  `completeDomainChoice`、`jensenCompletionWitness_source`、
  `jensenSpecialCase_isUFD_source`；另外 3 个在 Basic 层 Farley /
  analytic-irreducibility bridge。
- 原来的两个 bad quotient 大洞已经变为 checked wrappers：
  `quotientCompletionWitness_source` 和 `badQuotient_quasiCriterion_source`
  本身都不再含 `sorry`。
- 阶段一的第一字段已经完成为 `quotientCompletionEquiv_source`。父映射
  `completedRingToQuotientCompletion` 的满射、kernel 等式、descended map 的
  满射/单射/双射均已证明。
- 第二步已经开始：`BadQuotientSourceData.quotient_isNoetherian`、
  `BadQuotientSourceData.quotient_isDomain`、`quotient_nontrivial`、
  `quotient_mk_isLocalHom`、`quotient_isLocal` 和
  `quotient_noetherian_local_domain` 已证明。
- 第二步的维数一子目标已经完成。Lean 现在证明
  `BadQuotientSourceData.quotient_ringKrullDim_eq_one_source`：先从
  `JensenCompletionWitness` 取得 `ringKrullDim A = 2`，再由
  `q = span {a}`、`a ≠ 0`、`a` 是非零因子、`a ∈ maximalIdeal A`，
  使用 Mathlib 的主元降维定理得到
  `ringKrullDim (A/q)+1=2`，最后用 `WithBot ℕ∞` 的加一消去引理推出
  \(\dim(A/q)=1\)。`quotient_dimensionOneCriterionOnQuotientCompletion_source`
  现在也已经完成；它调用 Basic 层通用 source theorem
  `dimensionOne_weaklyQuasiComplete_iff_adicCompletion_source`。
- completion-quotient equivalence 的第一部分已经继续推进：已证明有限层
  quotient equivalence
  `A/(q + 𝔪^n) ≃ (A/q)/(𝔪(A/q))^n`，构造了兼容有限层映射和自然映射
  `AdicCompletion d.𝔪 d.A → quotientAdicCompletion d`，证明
  `qÂ` 落入 kernel，并得到下降映射
  `AdicCompletion d.𝔪 d.A ⧸ qÂ → quotientAdicCompletion d`。
  当前进一步证明了这个下降映射的满射、单射和双射，又建立了
  `AdicCompletion d.𝔪 (d.A ⧸ d.q)` 与 `quotientAdicCompletion d` 的
  comparison equivalence，证明父映射满射，并用 exactness + tensor
  presentation 关闭了 kernel 反包含。
- Farley 第一方向的 completion-neighborhood Krull-intersection 也已经继续推进：
  已证明 `adicCompletionPowerImage_one_ne_top`，证明了条件版本
  `adicCompletion_quotient_hausdorff_of_noetherian_local_completion`，并证明
  `adicCompletion_neighborhood_iInf_le_prime_of_hausdorff`。因此
  `adicCompletion_neighborhood_iInf_le_prime_source` 本身已经闭合；下一步要真正
  解决的是 `adicCompletion_quotient_hausdorff_source`，也就是证明
  \(\widehat A/P\) 对 completed maximal ideal topology 是 Hausdorff。
- `adicCompletion_quotient_hausdorff_source` 的完成环结构部分已经继续拆分：
  Lean 已证明 `mAhat = ker(Ahat -> A/m)`、
  `adicCompletionPowerImage_one_isMaximal`、
  `adicCompletionPowerImage_one_isHausdorff`，并证明
  `adicCompletion_quotient_hausdorff_of_noetherian_jacobson_completion` 以及
  `adicCompletionPowerImage_one_le_jacobson_of_isAdicComplete`。最新一轮又把
  这一点推进到所有有限层：`m^tAhat = ker(eval_t)`、
  `(mAhat)^t = m^tAhat`、`Ahat/(mAhat)^t ~= A/m^t`、completed/original
  neighborhood agreement、original precompleteness 到 `mAhat`-adic
  precompleteness 的转移、条件版 `mAhat`-adic completeness/localness，以及
  Noetherian+original-precomplete 条件版 quotient Hausdorff 都已经 checked。
  现在剩余的不是 maximality 或 Hausdorff separatedness，而是 `Ahat` 的
  Noetherian 性和原始 `𝔪`-adic precompleteness。

## 如果遇到阻塞

如果后续类似任务因 Mathlib completion quotient API 不足而阻塞，
不要回到大段 `sorry`。当前已经执行过有效路线：`quotientAdicCompletion`
用完全显式的基环实例固定为 `A/q` 自身的 adic completion，并注册了对应
`CommRing` instance；completion-quotient kernel 方向已经按如下方式完成：

- exact sequence `q -> A -> A/q` 的 module-level kernel statement；
- `AdicCompletion.map_exact` 能给出的完成后 exactness statement；已完成；
- completed submodule image 与扩张理想 `qAhat` 的识别；已完成；
- 把 module-level kernel 反包含转成 ring hom kernel 反包含；已完成；
- 用该 kernel 反包含关闭 quotient-by-kernel equivalence 的最后 source；已完成。

阶段一 bad quotient 专门化本身已经闭合。剩余的真正数学问题上移并拆分为
Farley 的 actual adic completion prime-contraction criterion，以及 Anderson
Corollary 2 中一维局部整环的 prime-contraction/analytic-irreducibility bridge。
Farley criterion 当前已经进一步拆成 `WeaklyQuasiCompleteBadChain` 与
`AdicCompletionBadPrime` 两个 obstruction object；两个 negation lemma 和
`weaklyQuasiComplete_iff_adicCompletion_primeContraction_source` 本身现在都是
checked wrappers。bad prime 生成 bad chain 的方向也已经继续展开成显式
contraction chain
`badPrimeContractionChain A 𝔪 P n = comap(A -> Ahat)(P ⊔ image(𝔪^n))`。
Lean 已经检查该链的 membership、下降性、基本包含关系，以及从
completion-neighborhood Krull-intersection 输入推出 contracted-chain
intersection 的 wrapper。剩余的是 Farley Proposition 1 中两个更深的
bad-prime 子输入，以及反方向 bad chain 生成 bad completion prime。
`dimensionOne_weaklyQuasiComplete_iff_adicCompletion_source` 本身也仍然是
checked wrapper。
此外，为了让该准则忠实于论文中的 maximal-adic completion，而不是任意
ideal-adic completion，新增了
`JensenCompletionWitness.adicIdeal_eq_maximalIdeal` 作为源环侧的
maximal-ideal 识别字段。`BadQuotientSourceData.adicIdeal_eq_maximalIdeal_source`
现在是 checked projection；quotient 侧的
`BadQuotientSourceData.quotient_adicIdeal_eq_maximalIdeal_source` 已经由 Mathlib
的 surjective local-hom maximal-ideal mapping theorem 证明。
