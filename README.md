# ComplexityReduction

A Lean 4 computational complexity reduction library providing formalization infrastructure for NP-completeness proofs. Based on mathlib (leanprover/lean4:v4.29.0).

## Module Structure

The root module `ComplexityReduction` aggregates the following 8 entry surfaces:

- Core — basic types such as `EncodedDecisionProblem`
- SAT — the 3SAT decision problem, Cook-Levin wrappers
- CSP — Boolean CSP formulas, constraints, encodings
- Schaefer — the Schaefer dichotomy theorem, tractability conditions
- Karp21 — enumeration and descriptors of the 21 Karp NPC problems
- Bridges — CostedReduction-to-TM bridges, soundness proofs
- Certificates — reduction certificates (costed / log-space)
- Targets — NPC target catalog and descriptors

## Build

```powershell
lake build complexityreduction
```

## Conventions

All declarations must be axiom-clean: `sorry` is forbidden, and `#print axioms` may only show `propext`, `Classical.choice`, `Quot.sound`.

> Chinese version: see [README.zh-CN.md](README.zh-CN.md).
