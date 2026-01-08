/-
  Collapse.lean
  =============

  Spencer-Brown Collapse Theorem

  If nothing is distinguishable, the universe collapses to at most one element.
  This formalizes Spencer-Brown's intuition that distinction
  is necessary for a non-trivial universe.
-/

import PhysicalLoF.Foundations.Distinction

namespace PhysicalLoF.Foundations

/-! ## Spencer-Brown Collapse Theorem (Theorem 1) -/

/--
  Spencer-Brown Collapse Theorem:
  If no two elements are distinguishable, the type is a subsingleton
  (contains at most one element).
-/
theorem spencer_brown_collapse
    {U : Type u}
    (h : ∀ a b : U, ¬Distinguishable a b) :
    Subsingleton U :=
  ⟨fun a b =>
    -- Since ¬Distinguishable a b means ¬(a ≠ b),
    -- which is equivalent to a = b by double negation
    Classical.byContradiction fun h_neq => h a b h_neq⟩

/-- Alternative formulation: if everything equals everything, there's only one thing -/
theorem all_equal_singleton
    {U : Type u}
    (h : ∀ a b : U, a = b) :
    Subsingleton U :=
  ⟨h⟩

/-- The void (empty type) trivially satisfies the collapse condition -/
theorem empty_trivially_collapses : Subsingleton Empty := inferInstance

end PhysicalLoF.Foundations
