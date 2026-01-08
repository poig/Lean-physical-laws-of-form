/-
  Distinction.lean
  ================

  The primitive concept: distinction / non-commutativity.

  Following Spencer-Brown's Laws of Form (1969), we take distinction
  as the primitive operation. Two things are distinguished if they
  are not equal.

  This is the foundation from which all structure derives.
-/

namespace PhysicalLoF.Foundations

/-! ## Primitive Definition -/

/-- Two elements are distinguishable if they are not equal -/
def Distinguishable {α : Type u} (a b : α) : Prop := a ≠ b

/-! ## Basic Properties -/

/-- Distinction is symmetric: if a differs from b, then b differs from a -/
theorem distinct_symm {α : Type u} {a b : α} : Distinguishable a b → Distinguishable b a :=
  fun h => fun heq => h heq.symm

/-- Nothing is distinguishable from itself (reflexivity of equality) -/
theorem distinct_irrefl {α : Type u} {a : α} : ¬Distinguishable a a :=
  fun h => h rfl

/-- If two things are equal, they cannot be distinguished -/
theorem eq_not_distinct {α : Type u} {a b : α} (h : a = b) : ¬Distinguishable a b :=
  fun hne => hne h

/-- Distinguishability implies inequality -/
theorem distinct_implies_ne {α : Type u} {a b : α} (h : Distinguishable a b) : a ≠ b := h

/-! ## The Bit: Minimal Distinction -/

/-- The bit {false, true} exhibits the minimal non-trivial distinction -/
theorem bit_distinguishable : Distinguishable false true := Bool.false_ne_true

/-- Zero and one are distinguishable (natural numbers) -/
theorem zero_one_distinguishable : Distinguishable (0 : Nat) 1 := Nat.zero_ne_one

/-! ## Logic Requires Distinction (Theorem 6) -/

/-- True and False are distinguishable - this is built into logic itself -/
theorem true_ne_false_prop : True ≠ False := fun h => h.mp trivial

/-- The Logical Distinction Theorem: Logic requires True ≠ False -/
theorem logical_distinction_theorem : Distinguishable True False := true_ne_false_prop

end PhysicalLoF.Foundations
