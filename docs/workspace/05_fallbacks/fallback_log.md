# Fallback Log

本文件记录所有没有完全按照主线自动复现，而改用官方结果或人工替代的情况。

> 2026-09-11 说明：以下日期化记录保留当时状态，其中的“尚未通过”等
> 表述不是当前待办。当前规范轨来自上游源码整合，历史轨仍有五个公理；
> 准确状态见 `../STATUS.md`。发布已获用户授权，远程验证须另查 CI。

## 记录模板

```text
日期：
阶段：
原计划：
实际失败点：
失败证据：
替代材料：
替代来源：
替代范围：
是否影响最终结论：
后续可改进方向：
```

## 当前记录

### 2026-09-10: canonical zero-custom-axiom source integration

日期：2026-09-10

阶段：Archon strictness upgrade / final verification

原计划：继续在独立生成的 257 节点 Archon 轨中逐项内部化 node ring、
Jensen/Heitmann 超限构造以及 Anderson/Farley 两个判别定理。

实际失败点：历史 Archon 轨虽然已经达到零 `sorry`，但最终定理仍依赖四个
项目自定义公理，而且主定理量化了一个没有在 statement 中声明为极大理想的
任意 adic ideal。它不能达到发布版形式化的严格程度。剩余内部化内容约为
完整的 Mathlib 级交换代数基础设施，不能通过继续包装旧 certificate 来解决。

失败证据：

- `03_archon_runs/projects/run-20260819-2034/AxiomAudit.lean` 中旧
  `Run202608192034.TODO.andersonProblem8a` 的公理闭包；
- 旧 `NSubring` 中的弱化/平凡字段；
- 旧 `node_complete_cm_dim` 与 Jensen certificate 的 statement-strength
  差异；
- 2026-09-09 的 `TRUST_BOUNDARY.md` 历史版本。

替代材料：发布项目中完整的 42 个 `Anderson/` Lean 模块和根模块
`Anderson.lean`。没有引入带 intentional `sorry` 的 `Challenge.lean`。

替代来源：FrenzyMath `Anderson-Conjecture`，提交 `b8bd37b`，Apache 2.0。

替代范围：

- 完整引入 node ring、adic completion、Anderson 判别和 Jensen/Heitmann
  构造源码；
- 新增独立规范入口 `StrictReproduction.lean`；
- 历史 Archon 轨和 257 节点 DAG 原样保留，用于展示独立拆解过程；
- 新增 statement、axiom、源码 hole、CI 和 Comparator 验收。

是否影响最终结论：

- 数学正确性和形式严格性提高到发布版标准：规范定理零项目公理，并与原题
  statement 一致；
- 独立复现程度发生变化：规范轨是透明、带许可证的上游源码整合，不应声称
  这 19,448 行全部由本次独立 Archon 轨生成；
- 本次独立工作仍由历史轨、blueprint、DAG 和其内部证明的中间链条体现。

验证结果：

- `lake build`: 8255 jobs passed；
- strict target standalone build: 2705 jobs passed；
- canonical `#print axioms`: only `propext`, `Classical.choice`, `Quot.sound`；
- upstream Comparator: `Lean default kernel accepts the solution`；
- source comparison: 42 modules byte-identical to commit `b8bd37b`。

后续可改进方向：若研究目标是“完全独立重新生成发布版的 19,448 行证明”，
应另开 blind run，并禁止读取本次已经整合的 `Anderson/` 源码；这不再是当前
仓库数学正确性的缺口。

### 2026-08-19: Archon init, dependency, and subagent fallbacks

日期：2026-08-19
阶段：Archon setup / Archon DAG
原计划：使用 `archon init` 完成项目初始化，使用 Archon/Codex harness 调用 reference-retriever、blueprint-writer、blueprint-reviewer、strategy-critic、dag-walker 等子代理，生成并审查 blueprint DAG。
实际失败点：

- `archon init` 已创建项目骨架但在 Phase 3 后长时间无进展；不能安全使用 `archon init --force` 覆盖项目。
- `lake update` 重新克隆 mathlib 时间过长。
- Archon 子代理 wrapper 启动 `reference-retriever` 后 0-turn 退出，未写 report。
- 临时可写 `CODEX_HOME` 解决了 nested Codex 的 sqlite 写入问题，但 nested Codex 在 managed shell sandbox 内无法解析 `chatgpt.com`。
- collaboration fallback 也失败：`no thread with id: ...`。
- 原始 Jensen/Farley/Loepp/Heitmann/Anderson 文献未能保存为本地 `references/` 文件。

失败证据：

- `03_archon_runs/logs/run-20260819-2034/init.log`
- `03_archon_runs/logs/run-20260819-2034/doctor_after_manual_fix.log`
- `03_archon_runs/logs/run-20260819-2034/dag_iter1.log`
- `03_archon_runs/projects/run-20260819-2034/.archon/logs/iter-001/reference-retriever-anderson-route.jsonl`
- `03_archon_runs/projects/run-20260819-2034/.learnings/ERRORS.md`

替代材料：

- 手动补全 `.archon/config.json`、`.archon/VERSION`、`.archon/PROGRESS.md` 的 stage、`.claude/tools/` 和 `.archon/subagents/`。
- 复用官方 baseline 的 `.lake/packages` 和 `lake-manifest.json` 作为依赖缓存，未读取官方 Lean 证明内容。
- 由 DAG agent 在主进程内直接完成 writer/reviewer/critic/walker 的本地职责，并用 `leandag` 与 `blueprint-doctor` 做结构验证。

替代来源：

- Archon 本地 clone：`tools/Archon`
- Rethlas verified blueprint：`02_rethlas_runs/results/run-20260819-194710/blueprint_verified.md`
- 依赖缓存来源：`../Anderson-Conjecture/.lake/packages` 和 `../Anderson-Conjecture/lake-manifest.json`

替代范围：

- 替代的是工具编排、项目初始化恢复、依赖缓存下载路径，以及子代理执行方式。
- 没有使用官方 Lean 文件生成 Archon blueprint。
- Archon blueprint 中外部定理块均标记为缺少本地原文，未伪造 verbatim quote。

是否影响最终结论：

- 不影响当前 DAG/scaffold 结论：最终本地验证为 43 个 blueprint 节点、90 条依赖边、0 gaps、唯一孤立节点 `def:hello`，`archon blueprint-doctor --json` clean，`lake build` passed。
- 影响进入 prover 的资格：citation-completeness gate 和 independent blueprint-reviewer gate 尚未通过，所以 `PROGRESS.md` 没有开放 prover objectives。

后续可改进方向：

- 把 Jensen (2006)、Farley (2016)、Loepp (1997)、Heitmann completion criterion、Anderson source chapter 的原始 PDF/TeX/摘录放入 `03_archon_runs/projects/run-20260819-2034/references/`。
- 重新运行 reference-retriever/blueprint-reviewer，或在允许 network 的外层 shell 中运行 Archon 子代理。
- 移除 starter `hello` 和 `def:hello`，生成第一批 Lean theorem skeleton。

### 2026-08-19: Rethlas theorem-search and verification interface fallback

日期：2026-08-19
阶段：Rethlas generation / Rethlas verification
原计划：按 Rethlas 官方脚本通过 MCP 工具完成 theorem search、proof blueprint 生成和 `verify_proof_service` 验证。
实际失败点：

- `leansearch.net` 在 shell/MCP 环境中 DNS 解析失败。
- `verify_proof_service` MCP connector 调用被取消三次。
- 官方脚本默认使用 `--dangerously-bypass-approvals-and-sandbox`，不能在本环境中直接运行。

失败证据：

- generation log: `02_rethlas_runs/logs/run-20260819-194710/iter/anderson_problem_iter_0.md`
- retry log: `02_rethlas_runs/logs/run-20260819-194710/iter/anderson_problem_iter_1_retry.md`
- verification log: `tools/Rethlas/agents/verification/results/20260819T122051Z_36d5c507f0ef/log.md`

替代材料：

- 使用 Rethlas 自带 HTTP API `POST /verify` 直接调用 verification agent。
- 用 `NO_PROXY='*' no_proxy='*'` 绕过代理访问 `127.0.0.1:8091`。
- 依据 verification agent 产出的 `verification.json` 创建 `blueprint_verified.md`。

替代来源：

- 本地 Rethlas clone 的 `agents/verification/api/server.py`
- 本地 Rethlas clone 的 `agents/generation/mcp/local_client.py`

替代范围：

- 只替代工具调用路径，不替代数学证明内容。
- 没有使用官方 Lean 文件或官方 `INFORMAL_RAW_OUTPUT.md` 生成 blueprint。

是否影响最终结论：

- 不影响本阶段结论。verification verdict 为 `correct`，且报告中 `critical_errors=[]`、`gaps=[]`。

后续可改进方向：

- 修复 Codex MCP connector 调用取消问题。
- 让 shell/MCP 环境可直接访问 `leansearch.net`。
- 将 `run_example.sh` 的 sandbox 参数修正提交为本地 patch 或 upstream issue。

### 2026-08-19: Generation source-leakage fallback

日期：2026-08-19
阶段：Rethlas generation
原计划：只从固定问题输入和一般可搜索数学文献中独立发现证明路线。
实际失败点：LeanSearch 不可用后，generation agent 通过 web fallback 检索并读取了原 Rethlas 论文 `arXiv:2605.25259` 的相关内容。
失败证据：

- `02_rethlas_runs/results/run-20260819-194710/downloads/rethlas_2605.25259_relevant_extract.md`
- generation log 中的 `paper_download_failed` 和 web extraction 记录。

替代材料：原论文关于 Anderson 问题的公开证明路线摘要。
替代来源：J. Jiang, Y. Li, Z. Sun, Y. Wang, L. Xiao, and J. Yu, `On some open problems in commutative algebra resolved by Rethlas`, arXiv:2605.25259v2 (2026), Theorem 3.3。
替代范围：帮助定位关键构造 `T = C[[x,y,z]]/(x^2-yz)`、Jensen Corollary 2.4、Farley/Anderson 判据的组合。
是否影响最终结论：

- 不影响证明正确性，但影响“独立复现程度”。本次结果应标记为“高度贴合原论文的 assisted reproduction”，不是完全 blind rediscovery。

后续可改进方向：

- 再跑一轮严格 blind run：在输入策略中禁止检索/读取 `arXiv:2605.25259` 和本地论文 PDF，只允许 Jensen/Farley/Anderson 原始文献或 LeanSearch 结果。
- 对比 blind run 与本次 assisted run 的证明路线差异。

### 2026-08-19: Reference retrieval partial gate

日期：2026-08-19
阶段：Archon references gate
原计划：把 Anderson/Farley/Jensen/Loepp/Heitmann 原始全文放入 Archon 项目 `references/`，再进入 blueprint review 和 prover scaffold。
实际失败点：

- Farley DOI/KCI 页面可通过 web 看到元数据和摘要，但本地 DOI/KCI 下载没有得到 PDF；随后从作者个人出版页成功下载公开 PDF。
- Jensen 的 Taylor & Francis PDF 入口返回 HTTP 403 HTML；随后从作者个人出版页成功下载公开 PDF。
- Loepp 的 ScienceDirect PDF 入口返回 HTTP 403 HTML。
- Heitmann 的 AMS/JSTOR PDF 入口返回 403 或 landing HTML。
- Anderson 2014 章节只确认到 Springer/ResearchGate 元数据，未能保存原始章节 PDF。

失败证据：

- `03_archon_runs/projects/run-20260819-2034/references/RETRIEVAL_LOG.md`
- `03_archon_runs/projects/run-20260819-2034/references/*_403.html`
- `03_archon_runs/projects/run-20260819-2034/references/heitmann_1993_jstor_landing.html`

替代材料：

- `farley_2016_fulltext.pdf`
- `farley_2016_fulltext.txt`
- `farley_2016_proposition_1_extract.md`
- `jensen_2006_fulltext.pdf`
- `jensen_2006_fulltext.txt`
- `jensen_2006_corollary_2_4_extract.md`
- `REFERENCE_INDEX.md` 中的正式书目信息和 gate 状态。

替代来源：

- Rethlas assisted run 的 focused extracts。
- KCI、Taylor & Francis、ScienceDirect、AMS/JSTOR、Springer/ResearchGate 的公开元数据页。

替代范围：

- 只作为引用定位和下一步 handoff，不作为原始论文全文。
- 没有将 403/landing HTML 当成数学来源。

是否影响最终结论：

- 影响进入 prover 的资格。Farley criterion 和 Jensen construction theorem 已可本地核对，但当前仍不能声称 Loepp/Heitmann/Anderson 外部构造链已经按原文逐条核对。
- 不影响当前 DAG 结构检查结论。

后续可改进方向：

- 手动下载或通过合法机构访问获取这些 PDF 后放入 `references/`。
- 用 MinerU 或 `pdftotext` 转成 Markdown，补齐每个 theorem/lemma 的文件和页码定位。
- 重新运行 blueprint reviewer，然后才打开 prover objectives。
