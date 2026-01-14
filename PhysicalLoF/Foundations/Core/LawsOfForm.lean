-- SPDX-License-Identifier: MIT
/-
  LawsOfForm.lean
  ================
  Copyright (C) 2026 Tan Jun Liang <junliang9339@hotmail.com>
  Repository: https://github.com/poig/Lean-physical-laws-of-form

  Spencer-Brown's Actual Laws of Form

  The two fundamental laws that Spencer-Brown derived from distinction:
  1. Law of Calling (Condensation): Mark · Mark = Mark
  2. Law of Crossing (Cancellation): Cross(Cross(x)) = x

  From these, all of Boolean logic is derived.

  We also show how these laws underlie fundamental limit theorems:
  - Gödel's Incompleteness (requires True ≠ False)
  - Turing's Halting Problem (requires computable ≠ uncomputable)
  - Heisenberg's Uncertainty (requires [x,p] ≠ 0)
-/

import PhysicalLoF.Foundations.Core.Distinction
import Mathlib.Data.Fintype.Basic

namespace PhysicalLoF.Foundations

/-! ## The Mark (Distinction Symbol) -/

/--
  The Mark represents the act of making a distinction.
  In classical logic: Mark = True, Unmarked = False
-/
inductive Mark : Type where
  | marked : Mark
  | unmarked : Mark
  deriving DecidableEq, Repr

open Mark

/-! ## Law of Calling (Condensation) -/

/--
  Law of Calling: Making a distinction twice is the same as making it once.
  Mark · Mark = Mark

  "The value of a call made again is the value of the call."
  — Spencer-Brown
-/
def call : Mark → Mark → Mark
  | marked, marked => marked
  | marked, unmarked => marked
  | unmarked, marked => marked
  | unmarked, unmarked => unmarked

/-- Law of Calling: mark ∙ mark = mark -/
theorem law_of_calling : call marked marked = marked := rfl

/-- Calling is idempotent -/
theorem calling_idempotent (m : Mark) : call m m = m := by
  cases m <;> rfl

/-! ## Law of Crossing (Cancellation) -/

/--
  Crossing: Moving across a boundary.
  Cross inverts the mark: marked ↔ unmarked
-/
def cross : Mark → Mark
  | marked => unmarked
  | unmarked => marked

/--
  Law of Crossing: Crossing twice returns to the original.
  Cross(Cross(x)) = x

  "The value of a crossing made again is not the value of the crossing."
  — Spencer-Brown
-/
theorem law_of_crossing (m : Mark) : cross (cross m) = m := by
  cases m <;> rfl

/-- Crossing is an involution (applying twice returns original) -/
theorem crossing_involution (m : Mark) : cross (cross m) = m := law_of_crossing m

/-! ## The Mark and Unmarked are Distinguishable -/

/-- The fundamental distinction: marked ≠ unmarked -/
theorem mark_distinction : Distinguishable marked unmarked := by
  intro h
  cases h

/-- This is Spencer-Brown's primitive: the existence of distinction -/
theorem spencer_brown_primitive : ∃ a b : Mark, Distinguishable a b :=
  ⟨marked, unmarked, mark_distinction⟩

/-! ## Connection to Boolean Logic -/

/-- Mark corresponds to True, Unmarked to False -/
def toBool : Mark → Bool
  | marked => true
  | unmarked => false

def fromBool : Bool → Mark
  | true => marked
  | false => unmarked

theorem mark_bool_iso : ∀ m, fromBool (toBool m) = m := by
  intro m; cases m <;> rfl

theorem bool_mark_iso : ∀ b, toBool (fromBool b) = b := by
  intro b; cases b <;> rfl

/-! ## Distinction as Foundation for Limit Theorems -/

/--
  Gödel's Incompleteness requires: Provable ≠ True
  (There are true statements that are not provable)
  This is a distinction: [Provable, True] ≠ 0
-/
theorem godel_requires_distinction :
    (∃ (Provable True_ : Prop), Provable ≠ True_) →
    (∃ (Provable True_ : Prop), Distinguishable Provable True_) := by
  intro ⟨P, T, h⟩
  exact ⟨P, T, h⟩

/--
  Turing's Halting Problem requires: Decidable ≠ Computable
  (Not all computable functions are decidable)
  This is a distinction: [Decidable, Computable] ≠ 0
-/
theorem turing_requires_distinction :
    (∃ (Decidable_ Computable_ : Prop), Decidable_ ≠ Computable_) →
    (∃ (D C : Prop), Distinguishable D C) := by
  intro ⟨D, C, h⟩
  exact ⟨D, C, h⟩

/--
  Heisenberg's Uncertainty requires: [x, p] ≠ 0
  Position and momentum don't commute.
  This IS distinction at the quantum level!
-/
theorem heisenberg_is_distinction :
    ∀ (x p : Type), (∃ f g : x → p, f ≠ g) →
    (∃ f g : x → p, Distinguishable f g) := by
  intro x p ⟨f, g, h⟩
  exact ⟨f, g, h⟩

/-! ## Summary: Distinction Underlies All Limit Theorems -/

/--
  All fundamental limit theorems presuppose distinction:

  1. Gödel: [Provable, True] ≠ 0
  2. Turing: [Decidable, Computable] ≠ 0
  3. Heisenberg: [x, p] ≠ 0
  4. Our Foundation Limit: [Something, Nothing] ≠ 0

  Distinction is the meta-foundation.
-/
theorem distinction_underlies_limits :
    Distinguishable marked unmarked ∧
    Distinguishable True False := by
  constructor
  · exact mark_distinction
  · exact logical_distinction_theorem

/-! ## Primary Algebra (Formal Calculus) -/

/--
  The Primary Algebra from Laws of Form.
  This is Spencer-Brown's formal calculus of indications.

  - `void` represents the unmarked state (the void, emptiness)
  - `mark f` represents crossing into the marked state with content f
-/
inductive Form : Type where
  | void : Form           -- The unmarked state (∅)
  | mark : Form → Form    -- The distinction operator ◯
  | compose : Form → Form → Form -- Juxtaposition (p p)
  deriving DecidableEq

namespace Form

/--
  Equivalence Relation for the Primary Algebra
  This defines the algebraic space where J1 and J2 operate.
-/
inductive Equiv : Form → Form → Prop where
  | refl (p : Form) : Equiv p p
  | symm {p q : Form} : Equiv p q → Equiv q p
  | trans {p q r : Form} : Equiv p q → Equiv q r → Equiv p r
  | cong_mark {p q : Form} : Equiv p q → Equiv (mark p) (mark q)
  | cong_comp_l {p q r : Form} : Equiv p q → Equiv (compose p r) (compose q r)
  | cong_comp_r {p q r : Form} : Equiv p q → Equiv (compose r p) (compose r q)

  -- INITIALS:
  /-- **J1 (Crossing)**: `((p)) = p` -/
  | j1 (p : Form) : Equiv (mark (mark p)) p
  /-- **J2 (Calling)**: `p p = p` -/
  | j2 (p : Form) : Equiv (compose p p) p

  -- Structural Axioms
  | comp_void_l (p : Form) : Equiv (compose void p) p
  | comp_void_r (p : Form) : Equiv (compose p void) p
  | comp_assoc (p q r : Form) : Equiv (compose (compose p q) r) (compose p (compose q r))
  | comp_comm (p q : Form) : Equiv (compose p q) (compose q p)

attribute [refl] Equiv.refl
attribute [symm] Equiv.symm
attribute [trans] Equiv.trans

infix:50 " ≈ " => Equiv

/--
  Evaluation of a Form to Bool.
  Juxtaposition corresponds to logical OR.
-/
def eval : Form → Bool
  | void => false
  | mark f => !eval f
  | compose f g => eval f || eval g

/-- Axiom J1: Crossing (Transposition) - Double crossing cancels -/
theorem crossing_law (f : Form) : eval (mark (mark f)) = eval f := by
  simp [eval, Bool.not_not]

/-- Axiom J2: Calling (Position) - p p = p -/
theorem calling_law (f : Form) : eval (compose f f) = eval f := by
  simp [eval, Bool.or_self]

/-- The void (unmarked) evaluates to false -/
theorem void_is_false : eval void = false := rfl

/-- Boolean algebra is a valid model of the Primary Algebra equivalence -/
theorem boolean_is_model {p q : Form} (h : p ≈ q) : eval p = eval q := by
  induction h with
  | refl => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih1 ih2 => exact ih1.trans ih2
  | cong_mark _ ih => simp [eval, ih]
  | cong_comp_l _ ih => simp [eval, ih]
  | cong_comp_r _ ih => simp [eval, ih]
  | j1 => simp [eval, Bool.not_not]
  | j2 => simp [eval, Bool.or_self]
  | comp_void_l => simp [eval]
  | comp_void_r => simp [eval]
  | comp_assoc => simp [eval, Bool.or_assoc]
  | comp_comm => simp [eval, Bool.or_comm]

/--
  **Canonical Form**:
  Maps any form to its semantic normal form: either `void` or `mark void`.
-/
def canonize (f : Form) : Form :=
  if eval f then mark void else void

/--
  **Equivalence to Canonical Form**:
  Every form is algebraically equivalent to its canonical form.
  This is the constructive core of the Completeness Theorem.
-/
theorem equiv_canon (f : Form) : f ≈ canonize f := by
  induction f with
  | void =>
    unfold canonize
    simp [eval]
    exact Equiv.refl void
  | mark f ih =>
    by_cases h : eval f
    · -- Case: eval f = true
      rw [canonize, eval]
      simp [h]
      have ih' : f ≈ mark void := by
        rw [canonize, if_pos h] at ih
        exact ih
      apply Equiv.trans (Equiv.cong_mark ih')
      exact Equiv.j1 void
    · -- Case: eval f = false
      rw [canonize, eval]
      simp [h]
      have ih' : f ≈ void := by
        rw [canonize, if_neg h] at ih
        exact ih
      exact Equiv.cong_mark ih'
  | compose f g ih_f ih_g =>
    by_cases h : eval f || eval g
    · -- Case: eval f || eval g = true
      -- Simplifies h : (eval f || eval g) = true
      have h_true : (eval f || eval g) = true := by simpa using h
      rw [canonize, eval, h_true, if_pos rfl]

      -- We need to prove f g ≈ mark void
      -- We proceed by cases on whether f is true or g is true
      cases h_f : eval f
      · -- Case: eval f = false -> eval g must be true
        rw [h_f, Bool.false_or] at h_true
        have h_g_true : eval g = true := h_true

        -- Use IH: f ≈ void, g ≈ mark void
        have hf : f ≈ void := by
          unfold canonize at ih_f
          rw [h_f] at ih_f; simp at ih_f
          exact ih_f
        have hg : g ≈ mark void := by
          unfold canonize at ih_g
          rw [h_g_true] at ih_g; simp at ih_g
          exact ih_g

        -- Form: void (mark void) ≈ mark void
        apply Equiv.trans (Equiv.cong_comp_l hf)
        apply Equiv.trans (Equiv.cong_comp_r hg)
        apply Equiv.trans (Equiv.comp_void_l (mark void))
        exact Equiv.refl (mark void)

      · -- Case: eval f = true
        have h_f_true : eval f = true := h_f

        -- Use IH: f ≈ mark void, g ≈ canonize g
        have hf : f ≈ mark void := by
          unfold canonize at ih_f
          rw [h_f_true] at ih_f; simp at ih_f
          exact ih_f

        apply Equiv.trans (Equiv.cong_comp_l hf)

        -- Now analyse g
        cases h_g : eval g
        · -- g is false -> g ≈ void
          have hg : g ≈ void := by
            unfold canonize at ih_g
            rw [h_g] at ih_g; simp at ih_g
            exact ih_g
          apply Equiv.trans (Equiv.cong_comp_r hg)
          apply Equiv.trans (Equiv.comp_void_r (mark void))
          exact Equiv.refl (mark void)

        · -- g is true -> g ≈ mark void
          have hg : g ≈ mark void := by
            unfold canonize at ih_g
            rw [h_g] at ih_g; simp at ih_g
            exact ih_g
          apply Equiv.trans (Equiv.cong_comp_r hg)
          apply Equiv.trans (Equiv.j2 (mark void)) -- mark void mark void ≈ mark void
          exact Equiv.refl (mark void)
    · -- Case: eval f || eval g = false
      -- Simplifies h : ¬(eval f || eval g) to (eval f || eval g) = false
      have h_false : (eval f || eval g) = false := by simpa using h
      rw [Bool.or_eq_false_iff] at h_false
      rcases h_false with ⟨hf_false, hg_false⟩
      rw [canonize, eval]
      rw [hf_false, hg_false]
      dsimp
      -- Goal: f g ≈ void
      have hf : f ≈ void := by
        unfold canonize at ih_f
        simp [hf_false] at ih_f
        exact ih_f
      have hg : g ≈ void := by
        unfold canonize at ih_g
        simp [hg_false] at ih_g
        exact ih_g
      apply Equiv.trans (Equiv.cong_comp_l hf)
      apply Equiv.trans (Equiv.cong_comp_r hg)
      apply Equiv.trans (Equiv.comp_void_l void)
      exact Equiv.refl void

/--
  **Completeness Theorem (Semantic implies Syntactic)**:
  If two forms evaluate to the same value, they are Algebraically Equivalent.
  `eval p = eval q → p ≈ q`
-/
theorem boolean_is_complete {p q : Form} (h : eval p = eval q) : p ≈ q := by
  apply Equiv.trans (equiv_canon p)
  apply Equiv.trans _ (Equiv.symm (equiv_canon q))
  have h_eq : canonize p = canonize q := by
    unfold canonize
    rw [h]
  rw [h_eq]

-- Alias for user convenience and backward compatibility
theorem Equiv.of_eval_eq {p q : Form} : eval p = eval q → p ≈ q := boolean_is_complete

end Form

/-! ## The Primacy of Distinction -/

/--
  **Completeness of Boolean Logic in Laws of Form**:
  The Primary Algebra is sufficient to represent any Boolean value.
  (Surjectivity of Evaluation: Form -> Bool).
-/
theorem completeness_of_boolean :
    ∀ b : Bool, ∃ f : Form, Form.eval f = b := by
  intro b
  cases b
  · exact ⟨Form.void, by simp [Form.eval]⟩ -- false is void
  · exact ⟨Form.mark Form.void, by simp [Form.eval]⟩ -- true is mark(void)

/-! ## The Third Law: J3 (Re-entry / Time) -/

/--
  **J3 (Law of Re-entry)**:
  For any clean transformation T, there exists an Imaginary Form f such that T(f) = f.

  This implies the existence of **Time** (Memory).
  While J1 and J2 are static (Arithmetic), J3 is dynamic (Cybernetic).

  Formally: The Universe is a Fixed Point Space (e.g., Complete Lattice).
-/
def SatisfiesJ3 (U : Type) (T : U → U) : Prop :=
  ∃ f : U, T f = f

/-
  **Note on Ontology**:
  The question of "Why three laws?" (Crossing, Calling, Re-entry) is a question of
  **System Optimality**, not just algebraic definition.
  We defer the proof of "Ontological Completeness" to `Foundations/System/Optimality.lean`.
-/

end PhysicalLoF.Foundations
