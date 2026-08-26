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

- `references/`  
  文献索引和资料完整性说明。论文 PDF 和提取出的全文文本只保存在本地工作区，
  没有上传到 GitHub，以避免仓库过大和版权问题。

- `lakefile.toml`、`lake-manifest.json`、`lean-toolchain`  
  Lean/Mathlib 环境配置。

## 当前进度

最近一次本地验证结果如下：

- blueprint 节点数：42
- 依赖边数：90
- 未匹配 Lean 声明：0
- blueprint gaps：0
- isolated nodes：0
- 当前仍有 `sorry` 的声明：10 个
- 已完成 Lean 代码量：12,663 characters
- `leandag` 估计剩余有限工作量：5,093 characters
- `lake build` 通过
- `leandag build --html` 通过
- `archon blueprint-doctor --json` 通过

也就是说，目前的状态是：证明路线、blueprint、Lean 声明和依赖图已经对齐；
整个 Lean 项目可以构建；但还有 10 个核心数学节点仍然需要继续形式化。

## 已完成的主要工作

当前工作已经完成了以下几部分：

1. 整理原论文路线，并把证明拆成 42 个 blueprint 节点。
2. 下载并核对所需文献，包括 Anderson、Farley、Jensen、Loepp、Heitmann。
3. 建立 Lean 项目，并把所有 blueprint 节点映射到 Lean 声明。
4. 将 quasi-complete 和 weakly quasi-complete 写成下降理想链的 Lean 定义。
5. 将 generic formal fiber 表达为 completion 中素理想对原环的零收缩条件。
6. 建立 node ring
   `C[[x,y,z]] / (x^2 - yz)` 和其中的 distinguished prime candidate。
7. 将最终结论改成真实的存在性命题，而不是 `True` 型占位命题。
8. 消除了若干纯连接型 `sorry`，包括从 bad quotient 推出最终非
   quasi-complete 的步骤。
9. 最近一轮把 `sorry` 从 18 个减少到 10 个，主要推进 Jensen 第二层构造接口。

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

## 剩余的主要数学工作

剩余 10 个 `sorry` 主要集中在三类问题：

1. 基础 completion / formal fiber 判别准则  
   包括 quasi-complete 与所有 quotient weakly quasi-complete 的等价、
   Farley 的 completion-prime criterion，以及一维情形下与 analytic
   irreducibility 的关系。

2. 显式 node ring 的代数性质  
   需要证明
   `C[[x,y,z]] / (x^2 - yz)` 是 domain、Noetherian local、二维，并且其中
   `Q = (x,y)` 是非主的高度一素理想。

3. bad quotient 的 completion 不是 domain  
   这是最后构造反例的关键步骤：需要把 quotient 的 completion 识别为
   `T / aT`，并利用扩张后的主理想不是素理想来证明 completion 非整环。

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
