# 实验协议：尽量贴合原论文的复现顺序

> 执行状态（2026-09-11）：已完成辅助运行及上游证明本地验收。历史 Archon 轨在零 `sorry`
> 后仍保留四个主结论外部边界；为满足“严格程度与发布版一致”的最终要求，
> 规范轨按本协议 fallback 规则引入了官方完整 Lean 模块。具体范围与独立性
> 影响已写入 `05_fallbacks/fallback_log.md`，最终对比已写入
> `04_comparison/comparison_template.md`。
> 下文的阶段指令保留原实验协议。规范 DAG、逐句映射和当前仓库自包含
> Comparator 尚待完成，远程状态以发布提交的 CI 为准。

## 目标

目标是尽可能复现论文中的流程，而不是只复现最终 Lean 项目：

```text
Rethlas informal agent
→ theorem search / proof blueprint
→ Archon formal agent
→ Lean 4 formalization
→ Comparator verification
```

## 主线流程

### Phase 1：问题输入固定

输入文件：

```text
01_problem_input/anderson_problem.md
```

输入要求：

- 只包含问题陈述、定义和允许引用的背景；
- 不包含官方 `INFORMAL_RAW_OUTPUT.md`；
- 不包含官方 Lean 代码；
- 不包含 `证明蓝图对照表.md` 中已经整理出的路线。

### Phase 2：Rethlas 非形式化证明生成

目标：

```text
anderson_problem.md
→ blueprint.md
→ blueprint_verified.md
```

预期命令形态，具体以安装后的 Rethlas README 为准：

```bash
cd <Rethlas>/agents/verification
python3 -m venv .venv
source .venv/bin/activate
pip install -r requirements.txt
uvicorn api.server:app --host 0.0.0.0 --port 8091
```

另一个终端：

```bash
cd <Rethlas>/agents/generation
python3 -m venv .venv
source .venv/bin/activate
pip install -r mcp/requirements.txt
PROBLEM_FILE=data/anderson_problem.md ./tests/run_example.sh
```

记录要求：

- 保存每轮日志；
- 保存生成的 `blueprint.md`；
- 如果 verifier 接受，保存 `blueprint_verified.md`；
- 如果失败，记录失败点，而不是直接覆盖。

### Phase 3：Rethlas 结果对比

比较新生成蓝图是否包含：

- 特殊环 `T = C[[x,y,z]]/(x^2-yz)`；
- 非主高度一素理想 `Q = (x,y)T`；
- Jensen 构造局部 UFD `A`；
- generic formal fiber 平凡；
- Farley/Anderson 的 WQC 判别；
- 坏商环 `A/(a)`；
- Anderson quotient criterion。

如果 Rethlas 无法生成可用蓝图，可以 fallback 到官方 `INFORMAL_RAW_OUTPUT.md`，但必须写入 `05_fallbacks/fallback_log.md`。

### Phase 4：Archon 形式化

目标是从 Rethlas 蓝图生成新的 Lean 项目，而不是直接复用官方 `Anderson-Conjecture`。

预期命令形态，具体以安装后的 Archon README 为准：

```bash
archon init <new-lean-project>
archon dag <new-lean-project>
archon loop <new-lean-project>
```

记录要求：

- 保存 Archon 配置；
- 保存每轮日志；
- 保存自动生成的 Lean 项目；
- 保留失败版本，不手动覆盖关键证据。

### Phase 5：验证

每个候选项目至少运行：

```bash
lake build
```

如果项目中形成了与官方 `Challenge.lean` 等价的 `main_theorem`，继续运行 Comparator。

### Phase 6：对比

使用：

```text
04_comparison/comparison_template.md
```

比较候选项目与官方项目的：

- 文件结构；
- 定理名；
- 关键数学策略；
- 自动生成程度；
- fallback 使用情况；
- 最终验证结果。

## Fallback 规则

fallback 只在主线无法推进时使用。优先级如下：

1. Rethlas 能生成，就使用 Rethlas 产物。
2. Rethlas 失败，使用官方 `INFORMAL_RAW_OUTPUT.md`。
3. Archon 某个模块失败，只 fallback 该模块对应的官方 Lean 文件。
4. Jensen 全构造失败，允许 fallback 官方 `Anderson/Jensen/*`，但必须继续尝试自行拼装主定理。
5. 如果完整 Archon 流程不可行，则保留当前第二层路线复现和官方 Comparator 结果作为最低可验证成果。

每次 fallback 都必须记录：

```text
阶段：
原计划：
失败原因：
替代材料：
替代来源：
对最终结论的影响：
```
