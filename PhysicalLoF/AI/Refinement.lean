-- SPDX-License-Identifier: MIT
/-
  Refinement.lean
  ===============

  Capacity expansion can only REFINE (split) equivalence classes, never merge them.
  This is the formal basis for curriculum learning.
-/

import PhysicalLoF.AI.Observation
import PhysicalLoF.AI.Policy

namespace PhysicalLoF.AI

open PhysicalLoF.Foundations

/-! ## Refinement Relation -/

/--
M₂ refines M₁ if every M₂-equivalence class is contained in some M₁-equivalence class.
Equivalently: if M₂ can distinguish a,b then so can M₁ (contrapositive: M₁-indistinguishable ⇒ M₂-indistinguishable is FALSE; we want the other direction).

Actually: refinement means M₂ distinguishes *at least* as much as M₁.
So: ObsEq M₂ a b → ObsEq M₁ a b  (M₂ collapses less, M₁ collapses more or equal).
-/
def Refines {U : Type u} (M₁ M₂ : BoundedMetaDistinction U) : Prop :=
  ∀ a b : U, ObsEq M₂ a b → ObsEq M₁ a b

/-- Refinement is reflexive. -/
theorem refines_refl {U : Type u} (M : BoundedMetaDistinction U) : Refines M M :=
  fun _ _ h => h

/-- Refinement is transitive. -/
theorem refines_trans {U : Type u} (M₁ M₂ M₃ : BoundedMetaDistinction U) :
    Refines M₁ M₂ → Refines M₂ M₃ → Refines M₁ M₃ :=
  fun h12 h23 a b h3 => h12 a b (h23 a b h3)

/--
If M₂ refines M₁, any policy valid for M₁ is also valid for M₂.
(Finer observation ⇒ can use coarser policies.)
-/
theorem policy_lifts_along_refinement {U : Type u} {A : Type v}
    (M₁ M₂ : BoundedMetaDistinction U) (hR : Refines M₁ M₂)
    (π : Policy U A) (hπ : RespectsObs M₁ π) :
    RespectsObs M₂ π :=
  fun hab => hπ (hR _ _ hab)

/-! ## Capacity Expansion as Refinement -/

/--
ExpandedCapacity from MetaDistinction refines the original (it uses the same observe map
embedded into a larger codomain, so equivalence classes are identical).
-/
theorem expanded_refines {U : Type u} (M : BoundedMetaDistinction U) (factor : Nat) (hf : factor ≥ 1) :
    Refines M (ExpandedCapacity M factor hf) := by
  intro a b hab
  -- ExpandedCapacity.observe = Fin.castLE ∘ M.observe
  -- So ObsEq (Expanded) means castLE (M.observe a) = castLE (M.observe b)
  -- castLE is IsInjectiveFin.castLE, so this implies M.observe a = M.observe b
  simp only [ObsEq, ExpandedCapacity] at hab ⊢
  have h1 : (M.observe a).val = (M.observe b).val := by
    have := congrArg Fin.val hab
    simp only [Fin.val_castLE] at this
    exact this
  exact Fin.ext h1

end PhysicalLoF.AI
