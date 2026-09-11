# Rethlas Runs

本目录用于记录 Rethlas 非形式化证明阶段。

## 目标

从：

```text
../01_problem_input/anderson_problem.md
```

生成：

```text
results/blueprint.md
results/blueprint_verified.md
```

## 建议记录结构

每次运行建立一个子目录：

```text
results/run-YYYYMMDD-HHMM/
├── problem.md
├── blueprint.md
├── blueprint_verified.md
├── verdict.json
└── notes.md
```

日志放入：

```text
logs/run-YYYYMMDD-HHMM/
```

## 运行前检查

- 确认没有把官方 `INFORMAL_RAW_OUTPUT.md` 放入 Rethlas 输入目录。
- 确认没有把官方 Lean 文件放入 Rethlas 输入目录。
- 确认 verification service 已启动。
- 确认模型/API 配置可用。

## 成功标准

最低成功标准：

- 生成一份 `blueprint.md`。

较好成功标准：

- 生成 verifier 接受的 `blueprint_verified.md`。

论文贴合标准：

- 蓝图自行发现并使用足够接近论文的关键结构和外部定理。

## 已完成运行

当前完成：

```text
results/run-20260819-194710/
├── RUN_MANIFEST.md
├── problem.md
├── blueprint.md
├── blueprint_verified.md
├── verification.json
└── downloads/
```

对应日志：

```text
logs/run-20260819-194710/
```

结论：

- Rethlas generation 产出完整 proof blueprint。
- Rethlas verification HTTP fallback verdict 为 `correct`。
- 本次为 assisted reproduction：generation 阶段通过 web fallback 读到了原 Rethlas 论文公开内容；详细说明见 `../05_fallbacks/fallback_log.md`。
