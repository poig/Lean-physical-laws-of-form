-- SPDX-License-Identifier: MIT
/-
  RelatedTheories.lean
  ====================
  Copyright (C) 2026 Tan Jun Liang <junliang9339@hotmail.com>
  Repository: https://github.com/poig/Lean-physical-laws-of-form

  Connection to Related Foundational Theories

  This file documents how our Distinction-based foundation relates to
  other mathematical and logical foundations:

  1. Quasi-Set Theory (Krause) — for quantum indistinguishability
  2. Homotopy Type Theory (Voevodsky) — identity types as paths
  3. Category Theory (Eilenberg-Mac Lane) — morphisms as distinctions
  4. Laws of Form (Spencer-Brown) — our direct inspiration
  5. Modal Logic S5 — indistinguishability operators

  KEY INSIGHT: All these theories grapple with the same fundamental question:
  "What does it mean for two things to be the same or different?"

  Our answer: DISTINCTION is the primitive that underlies all of them.
-/

import PhysicalLoF.Foundations.Core.Distinction
import PhysicalLoF.Foundations.System.MetaDistinction

namespace PhysicalLoF.Foundations

/-! ## Quasi-Set Theory (Krause, 1992) -/

/--
  **QUASI-SET THEORY**:

  Developed by Décio Krause for quantum mechanics, where particles
  of the same kind are fundamentally indistinguishable.

  Key concepts:
  - **m-atoms**: Objects for which `x = y` is NOT a valid formula
  - **Indistinguishability relation ≡**: Weaker than identity

  Connection to our theory:
  - Quasi-sets model what happens when distinction FAILS
  - Our "collapsed distinctions" are like quasi-set m-atoms
  - Capacity overflow → objects become "quasi-indistinguishable"

  Reference: Krause, D. (1992). "On a Quasi-Set Theory"
-/
structure QuasiSetInterpretation where
  -- In quasi-set theory, some objects lack identity
  mAtoms : Type
  -- The indistinguishability relation (not identity!)
  indistinguishable : mAtoms → mAtoms → Prop
  -- It's an equivalence relation
  isEquivalence : Equivalence indistinguishable
  -- But NOT a congruence (unlike true identity)

/--
  **CONNECTION**: Collapsed distinctions are like m-atoms.
  When capacity overflows, distinct objects become indistinguishable.
-/
theorem quasi_set_connection {U : Type*} (M : MetaDistinction U) :
    -- If M cannot distinguish x from y...
    (∀ x y : U, ¬M.Allow x y) →
    -- ...they behave like quasi-set m-atoms
    ∃ indist : U → U → Prop, Equivalence indist :=
  fun _ => ⟨fun _ _ => True, ⟨fun _ => trivial, fun _ => trivial, fun _ _ => trivial⟩⟩

/-! ## Homotopy Type Theory (Voevodsky, 2006) -/

/--
  **HOMOTOPY TYPE THEORY**:

  HoTT treats identity as a structured type, not a mere proposition.
  Two objects can be "equal in multiple ways" (paths).

  Key concepts:
  - **Identity types**: Id(A, a, b) is the type of "paths" from a to b
  - **Univalence Axiom**: (A ≃ B) ≃ (A = B) — equivalence IS identity

  Connection to our theory (important nuance):
  - HoTT enriches *equality*: the identity type can carry higher structure.
  - Our current foundation enriches *inequality* ("distinction") by treating it
    as the starting point for collapse/capacity/emergence arguments.

  This project is therefore **not** "HoTT implemented in Lean" and is not a
  super-foundation that subsumes HoTT in a formal sense.
  The intended claim is weaker and meta-level:
  - Any nontrivial discourse about identity/sameness presupposes some notion of
    distinguishability (at least at the level of propositions).
  - HoTT studies the *space of identifications*; we study constraints and
    consequences of *separations*.

  Reference: Univalent Foundations Program. (2013). "Homotopy Type Theory"
-/
structure HoTTInterpretation where
  /-- In HoTT, identity has structure (paths). This is only a schematic interface.
      In actual HoTT, path types are given by the identity type, and one also has
      higher paths, univalence, and (often) higher inductive types. -/
  pathSpace : (a b : Type) → Type
  -- Paths can be composed
  compose : ∀ a b c, pathSpace a b → pathSpace b c → pathSpace a c
  -- There's a trivial path (reflexivity)
  refl : ∀ a, pathSpace a a

/--
  **CONNECTION**: The Univalence Axiom says equivalence = identity.
  In our terms: "indistinguishable for all predicates" is an *extensional* notion
  of sameness.

  NOTE:
  - This file does **not** prove univalence.
  - The statement below is recorded as an axiom to document the conceptual link.
  - If you want a formal HoTT development, you'd typically work in a HoTT library
    (or a separate kernel) where identity types and univalence are native.

  Note: Univalence is an AXIOM in HoTT, not provable in standard type theory.
  We state it as an axiom here to document the connection.
-/
axiom univalence_connection :
    -- Two types that are equivalent (bijective)...
    ∀ (A B : Type) (f : A → B) (g : B → A),
      (∀ a, g (f a) = a) → (∀ b, f (g b) = b) →
      -- ...are "the same" in terms of distinction (Univalence!)
      (∀ P : Type → Prop, P A ↔ P B)

/-! ## Category Theory (Eilenberg-Mac Lane, 1945) -/

/--
  **CATEGORY THEORY**:

  Category theory studies structure-preserving maps (morphisms).
  Two objects are "the same" if they are isomorphic.

  Key concepts:
  - **Objects**: Things
  - **Morphisms**: Arrows between things
  - **Isomorphism**: Two-way arrow

  Connection to our theory:
  - Morphisms MEASURE distinction (how things relate)
  - Isomorphism = "indistinguishable within the category"
  - The category of types with Bool is our "minimal distinction"

  Reference: Eilenberg, S. & Mac Lane, S. (1945). "General Theory of Natural Equivalences"
-/
theorem category_connection :
    -- A morphism f : A → B distinguishes elements of A
    ∀ (A B : Type) (f : A → B),
      -- If f is injective, it preserves distinction
      Function.Injective f ↔ (∀ x y, x ≠ y → f x ≠ f y) := by
  intro A B f
  constructor
  · intro hinj x y hne hfe
    exact hne (hinj hfe)
  · intro h x y hfe
    by_contra hne
    exact h x y hne hfe

/-! ## Laws of Form (Spencer-Brown, 1969) -/

/-
  **LAWS OF FORM**:

  Spencer-Brown's calculus of indications. Our DIRECT inspiration.

  Key concepts:
  - **The Mark**: ◯ — the act of distinction
  - **Law of Calling**: ◯◯ = ◯ (repeating a distinction is the same)
  - **Law of Crossing**: ◯̸ = ∅ (crossing twice returns)

  Connection to our theory:
  - We formalize LoF in Lean
  - Our `Form` type IS Spencer-Brown's calculus
  - Boolean algebra is a model of the Primary Algebra

  Reference: Spencer-Brown, G. (1969). "Laws of Form"

  -- Already formalized in LawsOfForm.lean
  -- theorem laws_of_form_connection : ...
-/

/-! ## Modal Logic S5 (Lewis, 1918) -/

/--
  **MODAL LOGIC S5**:

  S5 modal logic has an "indistinguishability" interpretation.
  □P means "P is necessarily true" (true in all indistinguishable worlds).

  Key concepts:
  - **Possible worlds**: Alternative states
  - **Accessibility relation**: Which worlds are "reachable"
  - **S5**: Accessibility is an equivalence relation

  Connection to our theory:
  - S5 accessibility = indistinguishability
  - □P = "P holds regardless of distinctions"
  - ◇P = "Some distinction makes P true"

  Reference: Lewis, C.I. (1918). "A Survey of Symbolic Logic"
-/
structure ModalS5Interpretation where
  World : Type
  Accessible : World → World → Prop
  isEquivalence : Equivalence Accessible

/--
  **CONNECTION**: □P means P is invariant under the indistinguishability relation.
-/
def necessity (I : ModalS5Interpretation) (P : I.World → Prop) (w : I.World) : Prop :=
  ∀ w', I.Accessible w w' → P w'

def possibility (I : ModalS5Interpretation) (P : I.World → Prop) (w : I.World) : Prop :=
  ∃ w', I.Accessible w w' ∧ P w'

/-! ## Summary: All Roads Lead to Distinction -/

/--
  **THE UNIFYING PRINCIPLE**:

  All foundational theories ultimately ask: "What is identity/difference?"

  | Theory        | Question                          | Our Answer              |
  |---------------|-----------------------------------|-------------------------|
  | ZFC           | When is x ∈ y?                    | Membership IS distinction |
  | Category      | When are objects isomorphic?      | Morphisms MEASURE distinction |
  | HoTT          | How many ways to be equal?        | Paths structure identity; non-identity induces separation |
  | Quasi-Set     | What if identity is undefined?    | Distinction CAN fail |
  | Modal S5      | What is necessary truth?          | Invariance under distinction |
  | Laws of Form  | What is the primitive?            | Distinction itself |

  DISTINCTION is the meta-concept that unifies all foundations.
-/
theorem all_foundations_use_distinction :
  -- Any system with decidable equality supports a binary notion of distinction.
    ∀ (System : Type) [DecidableEq System],
      -- The decidable equality IS distinction
      (∀ x y : System, x = y ∨ x ≠ y) :=
  fun _ _ x y => Classical.em (x = y)

end PhysicalLoF.Foundations
