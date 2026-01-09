# Contributing to Lean-physical-laws-of-form

## Introduction
The goal of this project is to unify physics, logic, and complexity theory through the rigorous formalization of Distinction.

## Development Workflow
1.  **Build**: Run `lake build` to verify compilation.
2.  **Dependencies**: Use `lake update` to manage dependencies.
3.  **Branching**: Pull requests are welcome. Please use descriptive branch names.

## Style Guide
We follow the standard [Lean Mathlib Style Guide](https://leanprover-community.github.io/contribute/style.html), with specific additions:

### Headers
Every file MUST include the SPDX License Identifier and Copyright notice at the very top:
```lean
-- SPDX-License-Identifier: MIT
-- Copyright (C) 2026 Tan Jun Liang
-- Repository: https://github.com/poig/Lean-physical-laws-of-form
```

### Naming Conventions
*   **Types/Structures**: `CamelCase`
*   **Definitions/Theorems**: `camelCase`

## Rigorous Proof Standards
*   **Zero New Axioms**: All theoretical claims must be proven theorems. Axioms are strictly forbidden in `Foundations` without explicit prior approval.
*   **Standard Library**: Prefer `Mathlib` theorems (e.g., Pigeonhole Principle, Knaster-Tarski) over custom logic.
*   **No `sorry`**: Commits to `main` must not contain `sorry` in the `Foundations` directory.
