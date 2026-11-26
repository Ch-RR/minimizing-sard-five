# 核验记录

[逐条复核稿](minimizing-sard-five-audit.pdf) · [LaTeX 源文件](minimizing-sard-five-audit.tex) · [冻结运行结果](kernel_replay.json)

冻结运行编号为 `20261125T100321202560Z`，目标为 `MinimizingSard.Five.five_dimensional_metric_minimizing_sard`。运行使用 Lean 和 mathlib v4.24.0，重检了 150 个项目模块中的 2,602 条安全声明。日志中的 5 个跳过项均为 Lean 生成的递归辅助实现。依赖追踪可用 [InspectSkipped.lean](InspectSkipped.lean) 重跑。

在 [中文导读](../README.zh-CN.md) 的完整构建成功后，从 `lean/` 目录执行：

```sh
lake env lean --run ../audit/InspectSkipped.lean .proof-build
```

预期最后一行给出 `intersection = #[]`，表示主定理的项目依赖与上述五项的交集为空。主定理报告的公理依赖为 `propext`、`Classical.choice`、`Quot.sound`。

[Proposition63.lean](../lean/Proposition63.lean) 另行检查共同零测集命题及其依赖；[AuditAnchors.lean](../lean/AuditAnchors.lean) 列出复核稿中其他对应声明的公理依赖。这两份补充审计均由 [check.py](../lean/check.py) 在主重检结束后运行。
