# Official Mapping Targets

这些是官方 `Anderson-Conjecture` 中应作为对比目标的关键声明。

| 目标 | 官方位置 |
|---|---|
| 主规格 | `Challenge.lean:24`, `main_theorem` |
| 完整主定理 | `Anderson/Main.lean:855`, `main_theorem` |
| QC 定义 | `Anderson/Basic.lean:29`, `IsQuasiComplete` |
| WQC 定义 | `Anderson/Basic.lean:40`, `IsWeaklyQuasiComplete` |
| 解析不可约定义 | `Anderson/Basic.lean:46`, `IsAnalyticallyIrreducible` |
| WQC 判别 | `Anderson/QuasiCompleteRing/QuasiCompleteRing.lean:284`, `isWeaklyQuasiComplete_iff_primes_meet` |
| 一维 WQC 判别 | `Anderson/QuasiCompleteRing/QuasiCompleteRing.lean:502`, `dim1_wqc_iff_analyticallyIrreducible` |
| QC 商环判别 | `Anderson/QuasiCompleteRing/QuasiCompleteRing.lean:603`, `isQuasiComplete_iff_quotients_wqc` |
| `T` 的定义 | `Anderson/CompleteDomain/Domain.lean:21-24`, `conj_I`, `T` |
| `T` 是整环 | `Anderson/CompleteDomain/Domain.lean:416`, `T_isDomain` |
| `T` 是局部环 | `Anderson/CompleteDomain/LocalRing.lean:27`, `T_isLocalRing` |
| `T` 是 Noetherian | `Anderson/CompleteDomain/LocalRing.lean:205`, `T_isNoetherianRing` |
| `T` 完备 | `Anderson/CompleteDomain/LocalRing.lean:502`, `T_isAdicComplete` |
| `Q` 的定义 | `Anderson/CompleteDomain/CompleteDomain.lean:24`, `Q` |
| `Q` 是素理想 | `Anderson/CompleteDomain/CompleteDomain.lean:188`, `Q_isPrime` |
| `height(Q)=1` | `Anderson/CompleteDomain/CompleteDomain.lean:195`, `Q_height_one` |
| `Q` 非主 | `Anderson/CompleteDomain/CompleteDomain.lean:386`, `Q_not_isPrincipal` |
| `dim T = 2` | `Anderson/CompleteDomain/CompleteDomain.lean:530`, `T_ringKrullDim` |
| generic formal fiber 平凡 | `Anderson/Jensen/Defs.lean:21`, `HasTrivialGenericFormalFiber` |
| N-subring | `Anderson/Jensen/NSubring.lean:41`, `NSubring` |
| Jensen 特殊情形 | `Anderson/Jensen/Jensen.lean:679`, `jensen_special_case` |
| `A` 是 WQC | `Anderson/Main.lean:30`, `a_isWeaklyQuasiComplete` |
| 坏商环 | `Anderson/Main.lean:803`, `exists_prime_bad_quotient` |
