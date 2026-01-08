/-
  Collapse.lean
  =============

  Indistinguishability Collapse Theorem (renamed from "Spencer-Brown Collapse")

  Note: Spencer-Brown's actual "Collapse" is about self-reference resolution
  via oscillation. Our theorem is about how indistinguishability leads to
  a singleton type. We rename to avoid confusion.

  If nothing is distinguishable, the universe collapses to at most one element.
-/

import PhysicalLoF.Foundations.Distinction

namespace PhysicalLoF.Foundations

/-! ## Indistinguishability Collapse Theorem -/

/--
  Indistinguishability Collapse Theorem:
  If no two elements are distinguishable, the type is a subsingleton
  (contains at most one element).

  This is our theorem, distinct from Spencer-Brown's self-reference collapse.
-/
theorem indistinguishability_collapse
    {U : Type u}
    (h : ∀ a b : U, ¬Distinguishable a b) :
    Subsingleton U :=
  ⟨fun a b =>
    Classical.byContradiction fun h_neq => h a b h_neq⟩

/-- Alias for backward compatibility -/
abbrev spencer_brown_collapse := @indistinguishability_collapse

/-- Alternative formulation: if everything equals everything, there's only one thing -/
theorem all_equal_singleton
    {U : Type u}
    (h : ∀ a b : U, a = b) :
    Subsingleton U :=
  ⟨h⟩

/-- The void (empty type) trivially satisfies the collapse condition -/
theorem empty_trivially_collapses : Subsingleton Empty := inferInstance

end PhysicalLoF.Foundations
