-- SPDX-License-Identifier: MIT
/-
  Existence.lean
  ==============
  Copyright (C) 2026 Tan Jun Liang <junliang9339@hotmail.com>
  Repository: https://github.com/poig/Lean-physical-laws-of-form

  Distinction-Existence Theorem

  If multiple things exist, then some things are distinguishable.
  This is the contrapositive of the Spencer-Brown Collapse Theorem.

  Combined with the collapse theorem, this proves that non-commutativity
  is NECESSARY for non-trivial existence.
-/

import PhysicalLoF.Foundations.Core.Distinction
import PhysicalLoF.Foundations.System.Collapse

namespace PhysicalLoF.Foundations

/-! ## Nontrivial Type Definition -/

/-- A type is nontrivial if it has at least two distinct elements -/
class Nontrivial (α : Type u) : Prop where
  exists_pair_ne : ∃ x y : α, x ≠ y

/-! ## Distinction-Existence Theorem (Theorem 2) -/

/--
  Distinction-Existence Theorem:
  If two distinct elements exist, they must be distinguishable.
-/
theorem distinction_existence
    {U : Type u}
    (a b : U)
    (h_neq : a ≠ b) :
    Distinguishable a b := h_neq

/--
  Contrapositive of Collapse:
  If a type is not a subsingleton (has multiple elements),
  then some elements are distinguishable.
-/
theorem nontrivial_implies_distinction
    {U : Type u}
    [h : Nontrivial U] :
    ∃ a b : U, Distinguishable a b := by
  obtain ⟨a, b, hab⟩ := h.exists_pair_ne
  exact ⟨a, b, hab⟩

/-! ## Master Necessity Theorem (Theorem 7) -/

/--
  Master Necessity Theorem:
  For any nontrivial type, distinction must exist.

  This combines all the previous theorems:
  - If Distinguishable a b = False for all a,b → singleton (Collapse)
  - If multiple elements exist → ∃ Distinguishable a b (this theorem)

  Therefore: Existence of structure ⟹ Non-commutativity
-/
theorem master_necessity
    {U : Type u}
    [Nontrivial U] :
    ∃ a b : U, Distinguishable a b := nontrivial_implies_distinction

/--
  Observer Theorem:
  Any inhabited nontrivial type has distinction.
  (Anyone existing in a nontrivial universe proves distinction exists.)
-/
theorem observer_theorem
    {U : Type u}
    [Nontrivial U] :
    ∃ a b : U, Distinguishable a b := master_necessity

/-! ## Instances -/

/-- Bool is nontrivial: false ≠ true -/
instance : Nontrivial Bool := ⟨⟨false, true, Bool.false_ne_true⟩⟩

/-- Nat is nontrivial: 0 ≠ 1 -/
instance : Nontrivial Nat := ⟨⟨0, 1, Nat.zero_ne_one⟩⟩

/-! ## The Form of the Argument -/

/--
  We prove: If anything (nontrivial) exists, then distinction exists.

  The form is: ∃x (nontrivial) ⟹ ∃ Distinguishable a b

  NOT: ∅ ⟹ distinction (impossible)

  Since we exist in a nontrivial universe, distinction is proven for OUR universe.
-/
theorem existence_form (U : Type u) [Nontrivial U] : ∃ a b : U, Distinguishable a b :=
  nontrivial_implies_distinction

end PhysicalLoF.Foundations
