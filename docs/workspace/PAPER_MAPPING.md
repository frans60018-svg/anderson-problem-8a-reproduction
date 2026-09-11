# 证明蓝图对照表：从非形式化证明到 Lean 形式化

本文档对应复现工作的第二层目标：不只是确认最终 Lean 项目能构建，而是还原论文中“从证明思路到严格形式化证明”的结构。材料来源为：

- `Anderson-Conjecture/INFORMAL_RAW_OUTPUT.md`：Archon 输入的非形式化证明蓝图。
- `Anderson-Conjecture/Mathematical_Proof.pdf`：整理后的非形式化数学证明。
- `Anderson-Conjecture/Anderson/`：完整 Lean 4 形式化证明。
- `Anderson-Conjecture/Challenge.lean`：主定理规格文件。

当前文档没有声称重新运行了 Rethlas 或 Archon 的自动生成过程；它做的是“证明路线复现”：把数学证明步骤和最终 Lean 代码结构对应起来。

## 总体证明链

论文要证明：

```text
存在一个 Noetherian 局部环 R，使得 R 弱拟完备但不拟完备。
```

非形式化证明路线可以压缩成下面的链条：

```text
1. 构造特殊完全局部环 T = C[[x,y,z]]/(x^2-yz)
   T 是 2 维 Noetherian 完全局部整环，并有非主的高度 1 素理想 Q = (x,y)T。

2. 用 Jensen 的构造定理
   从 T 构造一个 Noetherian 局部 UFD A，使得 A 的 m-adic completion 同构于 T，
   且 A 的 generic formal fiber 是平凡的。

3. 用 Farley/Anderson 判别准则
   generic formal fiber 平凡推出 A 弱拟完备。

4. 取 Q 在 A 中的收缩 q = Q ∩ A
   由于 A 是 UFD 且 q 高度为 1，q = (a)，其中 a 是 A 中的素元。

5. 证明 A/(a) 不是弱拟完备
   因为 T/aT 不是整环，所以 A/(a) 的完成不是整环，即它不是 analytically irreducible。
   一维 Noetherian 局部整环中，弱拟完备等价于 analytically irreducible。

6. 用 Anderson 定理
   拟完备等价于所有商环弱拟完备。
   但 A/(a) 不是弱拟完备，所以 A 不是拟完备。

结论：A 弱拟完备但不拟完备。
```

在 Lean 中，主定理的最终入口是：

- `Anderson-Conjecture/Challenge.lean:24`：短规格文件中的 `main_theorem`。
- `Anderson-Conjecture/Anderson/Main.lean:855`：完整证明中的 `main_theorem`。

Comparator 已验证两者声明一致，且完整证明被 Lean kernel 接受。

## 总览对照表

| 非形式化证明块 | 数学作用 | Lean 入口 | 验证状态 |
|---|---|---|---|
| `lem:complete_domain_choice` | 构造 `T = C[[x,y,z]]/(x^2-yz)`，证明它是完整局部整环，并构造非主高度一素理想 `Q` | `CompleteDomain/Domain.lean`、`CompleteDomain/LocalRing.lean`、`CompleteDomain/CompleteDomain.lean` | 已由 `lake build` 验证 |
| `lem:jensen_special_case` | 对 `T` 应用 Jensen 构造，得到局部 UFD `A`，且 `Â ≅ T`，generic formal fiber 平凡 | `Jensen/Jensen.lean:679` 的 `jensen_special_case` | 已由 `lake build` 验证 |
| `lem:a_is_weak_and_has_bad_quotient` 第一部分 | 用 Farley 判别准则证明 `A` 弱拟完备 | `Main.lean:30` 的 `a_isWeaklyQuasiComplete`，依赖 `QuasiCompleteRing.lean:284` | 已由 `lake build` 验证 |
| `lem:a_is_weak_and_has_bad_quotient` 第二部分 | 找到素元 `a`，使 `A/(a)` 不是弱拟完备 | `Main.lean:803` 的 `exists_prime_bad_quotient` | 已由 `lake build` 验证 |
| `thm:main` | 用“拟完备 iff 所有商弱拟完备”推出 `A` 不是拟完备，并完成存在性定理 | `Main.lean:855` 的 `main_theorem`，依赖 `QuasiCompleteRing.lean:603` | 已由 `lake build` 和 Comparator 验证 |

## 逐步证明对照

### Step 0：定义拟完备、弱拟完备、解析不可约

非形式化证明先使用 Anderson 2014 的定义：

- quasi-complete：任意递降理想列最终落入交集加最大理想幂。
- weakly quasi-complete：只要求交集为零的递降理想列。
- analytically irreducible：完成环是整环。

Lean 对应：

| 数学内容 | Lean 文件与声明 | 说明 |
|---|---|---|
| 拟完备定义 | `Anderson/Basic.lean:29`，`def IsQuasiComplete` | 与 `Challenge.lean` 中的规格一致 |
| 弱拟完备定义 | `Anderson/Basic.lean:40`，`def IsWeaklyQuasiComplete` | 交集为 `⊥` 的特殊情形 |
| 解析不可约 | `Anderson/Basic.lean:46`，`def IsAnalyticallyIrreducible` | 定义为最大理想 adic completion 是 domain |
| 拟完备推出弱拟完备 | `Anderson/Basic.lean:50`，`IsQuasiComplete.isWeaklyQuasiComplete` | 后续一维判别和主定理中使用 |

### Step 1：构造特殊完成环 T

非形式化蓝图 `lem:complete_domain_choice` 选取：

```text
T = C[[x,y,z]]/(x^2 - yz)
M = (x,y,z)T
Q = (x,y)T
```

需要证明：

- `T` 是完整局部整环；
- `T` 是 Noetherian；
- `T` 的 Krull 维数为 2；
- `Q` 是高度一素理想；
- `Q` 不是主理想；
- `|T| = |T/M| = |C|`。

Lean 对应：

| 数学命题 | Lean 文件与声明 | 形式化处理 |
|---|---|---|
| 定义 `conj_I = (x^2-yz)` | `CompleteDomain/Domain.lean:21`，`def conj_I` | 把三元形式幂级数环中的生成元理想写成 `Ideal.span` |
| 定义 `T` | `CompleteDomain/Domain.lean:24`，`abbrev T` | `MvPowerSeries (Fin 3) ℂ ⧸ conj_I` |
| `T` 是整环 | `CompleteDomain/Domain.lean:416`，`instance T_isDomain` | 通过到 `C[[u,v]]` 的代换映射处理核，形式化了非形式化证明中的嵌入思路 |
| `T` 是局部环 | `CompleteDomain/LocalRing.lean:27`，`instance T_isLocalRing` | 证明商环继承局部结构 |
| `T` 是 Noetherian | `CompleteDomain/LocalRing.lean:205`，`instance T_isNoetherianRing` | 使用形式幂级数环的 Noetherian 性 |
| `T` 是 adic complete | `CompleteDomain/LocalRing.lean:502`，`instance T_isAdicComplete` | 形式化完整性 |
| `|T| = |C|` | `CompleteDomain/LocalRing.lean:696`，`theorem T_card_eq` | 对应蓝图里的基数计算 |
| 定义 `Q = (x,y)T` | `CompleteDomain/CompleteDomain.lean:24`，`def Q` | `Ideal.span` 两个像 |
| `Q` 是素理想 | `CompleteDomain/CompleteDomain.lean:188`，`theorem Q_isPrime` | 通过投影到 `C[[z]]` 的核证明 |
| `height(Q)=1` | `CompleteDomain/CompleteDomain.lean:195`，`theorem Q_height_one` | 用 Krull 主理想定理和素理想链 |
| `Q` 非主 | `CompleteDomain/CompleteDomain.lean:386`，`theorem Q_not_isPrincipal` | 这是非形式化证明中“`Q/MQ` 至少二维”的形式化替代路线 |
| `dim T = 2` | `CompleteDomain/CompleteDomain.lean:530`，`theorem T_ringKrullDim` | 用商环维数上界和 `⊥ < Q < maximal` 下界 |

这一块对应论文中 Archon “自动补非平凡 gap”的代表例子之一：证明 `T` 是整环时，非形式化证明写成与 `C[[u^2,uv,v^2]]` 同构，但 Lean 中需要显式处理代换映射、核和系数级别论证。

### Step 2：应用 Jensen 构造得到 A

非形式化蓝图 `lem:jensen_special_case` 引用 Jensen 2006 Corollary 2.4：

```text
存在局部 UFD A，使得 Â ≅ T，且 A 的 generic formal fiber 是 local with maximal ideal (0)。
```

在本仓库中，这个“引用外部定理”没有简单假设为 axiom，而是展开成大量 Lean 代码，形式化 Jensen/Heitmann/Loepp 的构造。

Lean 对应：

| 数学内容 | Lean 文件与声明 | 说明 |
|---|---|---|
| generic formal fiber 平凡的定义 | `Jensen/Defs.lean:21`，`def HasTrivialGenericFormalFiber` | 若完成环中素理想收缩为 0，则该素理想本身为 0 |
| N-subring 结构 | `Jensen/NSubring.lean:41`，`structure NSubring` | 包含 UFD、局部性、基数界、高度条件 |
| A-extension 结构 | `Jensen/NSubring.lean:82`，`structure IsAExtension` | 记录包含关系、素元保持、基数界 |
| 传递极限保持 N-subring | `Jensen/TransfiniteUnion.lean:181`，`transfinite_union_isNSubring` | 对应 Jensen 构造中的 limit ordinal 步 |
| close-up 过程 | `Jensen/CloseUp/CloseUp.lean:272`，`close_up` | 保证有限生成理想在扩张中闭合 |
| 关键 UFD 构造 | `Jensen/KrullDomain/UFDConstruction.lean:422`，`build_ufd_proof` | 用可形式化路线证明构造环仍为 UFD |
| 主递归构造 | `Jensen/Construction/Construction.lean:31`，`jensen_construction_p0_uncountable` | 完成 transfinite construction |
| Jensen 构造封装 | `Jensen/Jensen.lean:632`，`jensen_construction` | 把构造定理包装成适用于 `T` 的形式 |
| 特殊情形 | `Jensen/Jensen.lean:679`，`jensen_special_case` | 主证明直接使用的存在性结果 |

`jensen_special_case` 的 Lean 结论为：

```lean
∃ (A : Type) (_ : CommRing A) (_ : IsLocalRing A) (_ : IsDomain A)
  (_ : UniqueFactorizationMonoid A) (_ : IsNoetherianRing A),
  Nonempty (AdicCompletion (...) A ≃+* T) ∧
  HasTrivialGenericFormalFiber A
```

这与非形式化蓝图中的“存在 2 维局部 UFD A，完成为 T，generic formal fiber 平凡”基本对应。Lean 结论没有把“2 维”作为 `jensen_special_case` 输出的一部分；后续在需要商环维数时，通过完成环和 `T` 的维数另行证明。

### Step 3：由平凡 generic formal fiber 推出 A 弱拟完备

非形式化证明使用 Farley Proposition 1：

```text
Noetherian local domain R 弱拟完备
iff
完成环 R̂ 的每个非零素理想都与 R 非平凡相交。
```

如果 A 的 generic formal fiber 平凡，那么完成环中收缩为零的素理想只能是零理想。因此每个非零素理想都非零收缩，满足 Farley 判别准则。

Lean 对应：

| 数学内容 | Lean 文件与声明 | 说明 |
|---|---|---|
| Farley 判别准则 | `QuasiCompleteRing/QuasiCompleteRing.lean:284`，`isWeaklyQuasiComplete_iff_primes_meet` | WQC iff 完成环非零素理想非零收缩 |
| 对 A 应用该准则 | `Main.lean:30`，`a_isWeaklyQuasiComplete` | 用 `HasTrivialGenericFormalFiber A` 直接排除非零素理想零收缩 |

`a_isWeaklyQuasiComplete` 的证明非常短，说明这一段的主要工作已经被封装在 `isWeaklyQuasiComplete_iff_primes_meet` 和 `HasTrivialGenericFormalFiber` 定义里。

### Step 4：从 Q 的收缩得到素元 a

非形式化证明取：

```text
q = Q ∩ A
```

由于 generic formal fiber 平凡且 `Q ≠ 0`，所以 `q ≠ 0`。再由 faithfully flat completion 控制高度，得到 `height(q)=1`。因为 `A` 是 UFD，高度一素理想为主理想，于是：

```text
q = aA
```

其中 `a` 是 `A` 的素元。

Lean 对应：

| 数学内容 | Lean 文件与声明 | 说明 |
|---|---|---|
| `Q ≠ 0` | `Main.lean:82`，`Q_ne_bot` | 证明 `x` 在 `T` 中非零 |
| 环同构下非零理想收缩非零 | `Main.lean:93`，`comap_ringEquiv_ne_bot` | 用于把 `Q ≠ 0` 传到 `Â` |
| 收缩高度为 1 | `Main.lean:104`，`contraction_height_one` | 使用 completion 的 flatness/going-down |
| UFD 中高度一素理想主化 | `Main.lean:142`，`ufd_height_one_principal` | 从 `q` 得到素元 `a` |
| 组装坏商环存在性 | `Main.lean:803`，`exists_prime_bad_quotient` | 包含本 step 和下一 step |

这一块是非形式化证明中的“`Q∩A` 是高度一素理想，因此由 UFD 得到素元”的 Lean 化版本。

### Step 5：证明 A/(a) 不是弱拟完备

非形式化证明逻辑：

```text
aT ⊂ Q。
若 aT 是素理想，则因为 height(aT)=height(Q)=1，会推出 aT=Q。
但 Q 非主，矛盾。
所以 T/aT 不是整环。

又 A/(a) 的完成同构于 T/aT，
因此 A/(a) 不是 analytically irreducible。

A/(a) 是一维 Noetherian 局部整环；
一维情形下 WQC iff analytically irreducible。
所以 A/(a) 不是 WQC。
```

Lean 对应：

| 数学内容 | Lean 文件与声明 | 说明 |
|---|---|---|
| `A/(a)` 一维 | `Main.lean:482`，`quotient_prime_dim_one` | 用 `Â ≅ T` 和 `dim T = 2` 控制商环维数 |
| `A/(a)` 非解析不可约 | `Main.lean:572`，`quotient_not_analytically_irreducible` | 核心是把 `T/aT` 非整环传递到完成环 |
| 一维判别 | `QuasiCompleteRing/QuasiCompleteRing.lean:502`，`dim1_wqc_iff_analyticallyIrreducible` | Anderson Corollary 2 的形式化版本 |
| 存在坏商环 | `Main.lean:803`，`exists_prime_bad_quotient` | 输出素元 `a` 且 `¬ IsWeaklyQuasiComplete (A ⧸ (a))` |

这里对应论文提到的另一个形式化难点：非形式化证明中“完成与商交换”“不是 analytically irreducible”“一维判别”都需要在 Lean 中显式给出类型类实例、局部环结构、Noetherian 结构和维数证明。

### Step 6：由坏商环推出 A 不拟完备

非形式化证明使用 Anderson Theorem 5：

```text
Noetherian local ring R 拟完备
iff
R 的每个同态像都是弱拟完备。
```

因为已经构造出商环 `A/(a)` 不是弱拟完备，所以 `A` 不可能拟完备。

Lean 对应：

| 数学内容 | Lean 文件与声明 | 说明 |
|---|---|---|
| Anderson quotient 判别 | `QuasiCompleteRing/QuasiCompleteRing.lean:603`，`isQuasiComplete_iff_quotients_wqc` | QC iff 所有商 WQC |
| 最终拼装 | `Main.lean:855`，`main_theorem` | 取 `A` 为见证，给出 `WQC A ∧ ¬ QC A` |
| Comparator 规格 | `Challenge.lean:24`，`main_theorem` | 短规格文件，故意保留 `sorry` |

最终 Lean 主定理返回：

```lean
∃ (R : Type) (_ : CommRing R) (_ : IsLocalRing R) (_ : IsNoetherianRing R),
  IsWeaklyQuasiComplete R ∧ ¬ IsQuasiComplete R
```

这正是论文要证明的存在性反例。

## Lean 模块角色图

```text
Challenge.lean
  └─ 定义待验证主命题 main_theorem

Anderson.lean
  └─ import Anderson.Main

Anderson/Main.lean
  ├─ a_isWeaklyQuasiComplete
  ├─ exists_prime_bad_quotient
  └─ main_theorem

Anderson/Basic.lean
  ├─ IsQuasiComplete
  ├─ IsWeaklyQuasiComplete
  └─ IsAnalyticallyIrreducible

Anderson/QuasiCompleteRing/QuasiCompleteRing.lean
  ├─ isWeaklyQuasiComplete_iff_primes_meet
  ├─ dim1_wqc_iff_analyticallyIrreducible
  └─ isQuasiComplete_iff_quotients_wqc

Anderson/CompleteDomain/*
  ├─ T = C[[x,y,z]]/(x^2-yz)
  ├─ T_isDomain
  ├─ T_isLocalRing
  ├─ T_isNoetherianRing
  ├─ T_isAdicComplete
  ├─ Q_isPrime
  ├─ Q_height_one
  ├─ Q_not_isPrincipal
  └─ T_ringKrullDim

Anderson/Jensen/*
  ├─ HasTrivialGenericFormalFiber
  ├─ NSubring / IsAExtension
  ├─ close_up
  ├─ transfinite_union_isNSubring
  ├─ jensen_construction_p0_uncountable
  └─ jensen_special_case
```

## 与原论文自动化流程的关系

当前第二层复现覆盖的是：

```text
非形式化证明蓝图
→ Lean 模块分解
→ 关键定理声明
→ 最终形式化证明
→ Comparator 验证
```

这份第二层对照文档本身不覆盖以下过程；后续执行记录位于第三层工作区：

```text
Rethlas 自动发现 Jensen/Farley 等外部定理
→ Archon 自动生成 Lean scaffold
→ Archon 多轮自动修补所有证明
```

后续第三层已在 `03_full_pipeline_reproduction/` 执行 Rethlas/Archon
辅助复现。该运行保留了五个外部公理，最终完整规范源码来自上游整合；
本对照表是关键声明级阅读材料，尚非逐句论文审计或完整 canonical DAG。

## 当前复现结论

在本机当前文件夹中，已经完成：

```text
非形式化证明路线梳理
Lean 关键模块对应
lake build 成功
Comparator 成功
```

第二层已建立关键证明步骤与源码的对应关系。自动生成的后续运行、辅助输入、
历史公理与上游整合情况，以第三层工作区当前状态说明为准。
