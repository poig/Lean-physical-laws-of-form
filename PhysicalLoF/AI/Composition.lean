-- SPDX-License-Identifier: MIT
/-
  Composition.lean
  ================

  Governors (safety layers) can be composed, and the composition enforces the intersection
  of their allowed sets.
-/

import PhysicalLoF.AI.Governor

namespace PhysicalLoF.AI

/-! ## Governor Composition -/

/-- Compose two governors: apply G₁ first, then G₂. -/
def composeGovernor {A : Type u} (G₁ G₂ : Governor A) : Governor A where
  clamp := G₂.clamp ∘ G₁.clamp

/-- Sequential composition enforces the intersection of allowed sets (if both enforce cleanly). -/
theorem compose_enforces {A : Type u} (G₁ G₂ : Governor A) (S₁ S₂ : Set A)
    (h₁ : Enforces G₁ S₁) (h₂ : Enforces G₂ S₂) :
    ∀ a, (composeGovernor G₁ G₂).clamp a ∈ S₂ := by
  intro a
  simp only [composeGovernor, Function.comp_apply]
  exact h₂.1 (G₁.clamp a)

/-- If an action is already in S₂ after G₁, then G₂ leaves it unchanged. -/
theorem compose_preserves {A : Type u} (G₁ G₂ : Governor A) (S₁ S₂ : Set A)
    (h₁ : Enforces G₁ S₁) (h₂ : Enforces G₂ S₂)
    (a : A) (ha : G₁.clamp a ∈ S₂) :
    (composeGovernor G₁ G₂).clamp a = G₁.clamp a := by
  simp only [composeGovernor, Function.comp_apply]
  exact h₂.2 (G₁.clamp a) ha

/-! ## Parallel Composition (for multi-output systems) -/

/-- Compose governors on a product space. -/
def parallelGovernor {A B : Type u} (GA : Governor A) (GB : Governor B) : Governor (A × B) where
  clamp := fun ⟨a, b⟩ => (GA.clamp a, GB.clamp b)

theorem parallel_enforces {A B : Type u} (GA : Governor A) (GB : Governor B)
    (SA : Set A) (SB : Set B)
    (hA : Enforces GA SA) (hB : Enforces GB SB) :
    ∀ ab, (parallelGovernor GA GB).clamp ab ∈ Set.prod SA SB := by
  intro ⟨a, b⟩
  simp only [parallelGovernor, Set.mem_prod_eq]
  exact ⟨hA.1 a, hB.1 b⟩

end PhysicalLoF.AI
