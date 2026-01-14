-- SPDX-License-Identifier: MIT
/-
  Galois.lean
  ===========
  Copyright (C) 2026 Tan Jun Liang <junliang9339@hotmail.com>
  Repository: https://github.com/poig/Lean-physical-laws-of-form

  Algebraic Indistinguishability and Galois Theory

  KEY INSIGHT:
  In Galois theory, roots of a polynomial are "algebraically indistinguishable"
  if any automorphism of the splitting field permutes them.

  Connection to Capacity Overflow:
  - Simple Galois group: roots are easily distinguished → solvable by radicals
  - Complex Galois group: roots are "too symmetric" → UNSOLVABLE (capacity overflow!)

  The unsolvability of the quintic is a capacity overflow:
  The Galois group S₅ is too large (non-solvable), meaning the algebraic
  "observation capacity" of radicals cannot distinguish the roots.

  This file USES Mathlib's official Abel-Ruffini formalization.
-/

import Mathlib.FieldTheory.AbelRuffini
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.GroupTheory.Solvable
import PhysicalLoF.Foundations.Core.Distinction
import PhysicalLoF.Foundations.System.MetaDistinction
import Mathlib.Data.Nat.Basic

namespace PhysicalLoF.Foundations

open Polynomial

/-! ## Using Mathlib's Abel-Ruffini -/

variable {F E : Type*} [Field F] [Field E] [Algebra F E]

/--
  **BRIDGE TO MATHLIB**: Mathlib's `IsSolvableByRad` is the official definition.

  An element is solvable by radicals if it can be expressed using:
  - Field operations (+, -, ×, /)
  - n-th roots
-/
example (α : E) : IsSolvableByRad F α ↔ α ∈ solvableByRad F E := Iff.rfl

/-! ## Algebraic Indistinguishability -/

/--
  Two elements of a field extension are algebraically indistinguishable
  over the base field K if there exists a K-automorphism mapping one to the other.

  This is the same as "being conjugates" under the Galois group.
-/
def AlgebraicallyIndistinguishable (K L : Type*) [Field K] [Field L] [Algebra K L]
    (x y : L) : Prop :=
  ∃ σ : L ≃ₐ[K] L, σ x = y

/-! ## The Abel-Ruffini Theorem (from Mathlib) -/

/--
  **MATHLIB'S ABEL-RUFFINI THEOREM**:

  If an irreducible polynomial has a root solvable by radicals,
  then its Galois group must be solvable.

  Contrapositive: Non-solvable Galois group → NOT solvable by radicals.
-/
theorem abel_ruffini_from_mathlib {α : E} {q : F[X]}
    (q_irred : Irreducible q) (q_aeval : aeval α q = 0)
    (hα : IsSolvableByRad F α) : IsSolvable q.Gal :=
  solvableByRad.isSolvable' q_irred q_aeval hα

/-! ## Capacity Overflow Interpretation -/

/--
  **CAPACITY OVERFLOW FORM**:

  The symmetric group S₅ is NOT solvable.
  Therefore, polynomials with Galois group S₅ are NOT solvable by radicals.

  This is capacity overflow: The "radical observer" cannot distinguish roots
  because the symmetry group is too complex (non-solvable).
-/
theorem galois_capacity_overflow :
    ¬IsSolvable (Equiv.Perm (Fin 5)) := by
  -- Use the specific theorem for S5
  exact Equiv.Perm.fin_5_not_solvable

/--
  **THE GALOIS PRINCIPLE**:

  From K's perspective, algebraically indistinguishable elements
  cannot be distinguished by any K-polynomial.
-/
theorem galois_hidden_distinction (K L : Type*) [Field K] [Field L] [Algebra K L]
    (x y : L) (h : AlgebraicallyIndistinguishable K L x y) (p : K[X]) :
    aeval x p = 0 ↔ aeval y p = 0 := by
  obtain ⟨σ, hσ⟩ := h
  constructor
  · intro hx
    -- Key: For AlgEquiv σ, we have σ.toAlgHom.comp (aeval x) = aeval (σ x)
    -- So σ (aeval x p) = (σ.toAlgHom.comp (aeval x)) p = aeval (σ x) p
    have key : σ (aeval x p) = aeval (σ x) p := by
      rw [aeval_algHom_apply]
    rw [← hσ, ← key, hx, map_zero]
  · intro hy
    -- Reverse direction: use σ⁻¹
    have hσ' : σ.symm y = x := by simp [← hσ]
    have key : σ.symm (aeval y p) = aeval (σ.symm y) p := by
      rw [aeval_algHom_apply]
    rw [← hσ', ← key, hy, map_zero]

/-! ## Connection to Meta-Distinction -/

/--
  The Galois group measures the "symmetry" between roots.
  Larger Galois group = more indistinguishable roots = more symmetric.
-/
noncomputable def GaloisSymmetryCapacity (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] : ℕ :=
  Fintype.card (L ≃ₐ[K] L)

/--
  From the perspective of the base field K,
  conjugate roots are "the same" — they satisfy the same polynomial equations.

  The Galois group is the structure that tracks these "hidden" distinctions.
-/
noncomputable def FieldAsMetaDistinction (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] :
    BoundedMetaDistinction L where
  Allow := fun x y => ¬AlgebraicallyIndistinguishable K L x y
  Cost := fun _ _ => 1
  Capacity := GaloisSymmetryCapacity K L
  observe := fun x => ⟨0, by
    -- GaloisSymmetryCapacity K L > 0 because identity always exists
    unfold GaloisSymmetryCapacity
    exact Fintype.card_pos⟩
  cap_pos := by
    -- The identity automorphism always exists, so card >= 1
    unfold GaloisSymmetryCapacity
    exact Fintype.card_pos

end PhysicalLoF.Foundations
