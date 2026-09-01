# ComplexityReduction

Lean 4 计算复杂度归约库，为 NP 完全性证明提供形式化基础设施。基于 mathlib（leanprover/lean4:v4.29.0）。

## 模块结构

根模块 `ComplexityReduction` 聚合以下 8 个入口面：

- Core — EncodedDecisionProblem 等基础类型
- SAT — 3SAT 判定问题、Cook-Levin 包装
- CSP — 布尔 CSP 公式、约束、编码
- Schaefer — Schaefer 二分法定理、可处理条件
- Karp21 — 21 个 Karp NPC 问题枚举与描述符
- Bridges — CostedReduction 到 TM 桥接、可靠性证明
- Certificates — 归约证书（costed / log-space）
- Targets — NPC 目标目录与描述符

## 构建

```powershell
lake build complexityreduction
```

## 约定

所有声明必须 axiom-clean：禁止 sorry，#print axioms 只允许 propext、Classical.choice、Quot.sound。
