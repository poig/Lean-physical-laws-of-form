# Physical Laws of Form

**Lean 4 formalization of Spencer-Brown's distinction extended to physics and computation**

[![Lean](https://img.shields.io/badge/Lean-4.27-blue)](https://lean-lang.org/)
[![Mathlib](https://img.shields.io/badge/Mathlib-latest-purple)](https://github.com/leanprover-community/mathlib4)
[![License](https://img.shields.io/badge/License-MIT-green)](LICENSE)

## Overview

This repository contains machine-verified proofs that **distinction [A,B] ≠ 0 is the foundation of all structure** — from logic to physics to computation.

### Core Claims (Proven)

1. **Non-commutativity is necessary for existence** (Master Necessity Theorem)
2. **If nothing is distinguishable, the universe collapses** (Indistinguishability Collapse)
3. **Distinction is the optimal foundation** (Foundation Limit Theorem)
4. **All impossibility theorems presuppose distinction** (Gödel, Turing, Heisenberg)

## Attribution

This work extends **George Spencer-Brown's *Laws of Form* (1969)**.

> "We take as given the idea of distinction and the idea of indication, 
> and that we cannot make an indication without drawing a distinction."
> — Spencer-Brown (1969)

---

## The Hierarchy of Structure

```
Level 0:   VOID
    ↓
Level 1:   DISTINCTION             [A, B] ≠ 0
    ↓
Level 2:   META-DISTINCTION        Structure / Constraint
    ↓
Level 3:   THE GRAND TRILOGY       Application of Level 2
           - Logic (Gödel: Hidden Distinction)
           - Complexity (P vs NP: Resource Constraint)
           - Emergence (The Loop: Self-Organization)
    ↓
Level 4:   PHYSICS                 Standard Model
```

---



## Installation

```bash
# Clone the repository
git clone https://github.com/poig/Lean-physical-laws-of-form.git
cd Lean-physical-laws-of-form

# Download Mathlib cache
lake exe cache get

# Build
lake build

# upload compile cache
lake exe cache put
```

## Project Structure

```
Lean-physical-laws-of-form/
├── PhysicalLoF/
│   ├── Foundations/
│   │   ├── Distinction.lean      # Level 1: [A,B] ≠ 0
│   │   ├── Collapse.lean         # Level 1: Indistinguishability → singleton
│   │   ├── Existence.lean        # Level 1: Master Necessity
│   │   ├── Optimality.lean       # Level 1: Foundation Limit Theorem
│   │   ├── LawsOfForm.lean       # Level 1: Spencer-Brown's Laws
│   │   └── Transformation.lean   # Level 2: Morphisms, f : A → B
│   └── ImpossibilityTheorems.lean # Gödel, Turing, Heisenberg
├── PhysicalLoF.lean              # Main library entry
├── Main.lean                     # Executable entry
├── lakefile.lean                 # Build configuration (Mathlib)
└── lean-toolchain                # Lean 4.27
```

---

## Key Theorems

| Theorem | Description |
|---------|-------------|
| `master_necessity` | Nontrivial type ⟹ ∃ distinguishable elements |
| `indistinguishability_collapse` | No distinction ⟹ Subsingleton |
| `distinction_is_optimal` | Distinction is the minimal foundation |
| `foundation_limit` | Optimal foundation exists |
| `law_of_calling` | Mark · Mark = Mark |
| `law_of_crossing` | Cross(Cross(x)) = x |
| `distinction_meta_foundation` | All impossibility theorems require distinction |
| `noncommuting_distinguishable` | [f,g] ≠ 0 ⟹ f∘g ≠ g∘f are distinguishable |

---

## Philosophy: Engineering Theory of Everything

This project embodies an **honest** approach to foundations:

1. **We admit no complete ToE can exist** (Gödel, observer inclusion)
2. **We prove this is unknowable** (Foundation Limit Theorem)
3. **We identify the optimal approximation** (Distinction)
4. **We machine-verify everything** (Lean 4)
5. **We asymptotically improve** (open source, collaborative)

---

## References

- Spencer-Brown, G. (1969). *Laws of Form*. London: Allen & Unwin.
- Kauffman, L. (1987). *Self-reference and recursive forms*.
- Meiburg, A. (2024). *Quantum Information in Lean*. GitHub.
- Saito, S. (2024). *Formalized Formal Logic*. GitHub.

---

## License

MIT License - Copyright (c) 2026 Tan Jun Liang

## Contributing

Contributions welcome! Especially:
- Category theory formalizations
- Lie algebra and group theory
- Physics interpretations
- Complexity theory connections