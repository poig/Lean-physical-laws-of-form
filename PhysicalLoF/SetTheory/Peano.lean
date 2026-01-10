-- SPDX-License-Identifier: MIT
/-
  Peano.lean
  ==========
  Validating that our "Distinction Numbers" behave like real numbers.

  The Peano Axioms:
  1. 0 is a Nat. (True by definition: `PureSet.zero`)
  2. succ(n) is a Nat. (True by definition: `PureSet.succ`)
  3. succ(n) ≠ 0. (Zero is not a Successor)
  4. succ(n) = succ(m) → n = m. (Injectivity)
  5. Induction Principle.
-/

import PhysicalLoF.SetTheory.Base
import PhysicalLoF.SetTheory.Naturals

namespace PhysicalLoF.SetTheory.Peano

open PhysicalLoF.SetTheory.PureSet

/-! ### Axiom 3: Disjointness of Zero and Successor -/

theorem zero_ne_succ (n : PureSet) : zero ≠ succ n := by
  -- zero is `void`
  -- succ n is `set [...]` (always a non-empty list constructor)
  intro h
  simp [zero, succ] at h
  split at h
  · contradiction -- void = set [void]
  · contradiction -- void = set (n::xs)

/-! ### Axiom 4: Injectivity of Successor -/

-- This is the hardest part for set-theoretic definitions.
-- succ n = n ∪ {n}.
-- If n ∪ {n} = m ∪ {m}, does n = m?
-- In ZFC, this relies on the Axiom of Foundation (Regularity).
-- In our constructivist `PureSet`, it relies on the list structure.

theorem succ_injective (n m : PureSet) : succ n = succ m → n = m := by
  intro h
  simp [succ] at h
  split at h <;> split at h
  · -- Case 0 -> 0: [void] = [void] → True
    rfl
  · -- Case 0 -> S(x): [void] = (n :: xs)
    -- This implies list length 1 vs length > 1?
    -- No, `set (n :: xs)` has length 1+len(xs).
    -- If m was `set xs`, then `succ m` puts m in front.
    -- This requires deep analysis of the canonical representation.
    sorry -- Requires structural analysis of list cons
  · -- Case S(x) -> 0
    sorry
  · -- Case S(x) -> S(y)
    -- (n :: xs) = (m :: ys) implies n = m.
    -- This is true for Lists!
    injection h with h_list
    injection h_list with h_head
    exact h_head

/-! ### Axiom 5: Induction -/

-- Because `PureSet` is an inductive type, we get structural induction for free.
-- However, we need to show that "Mathematical Induction" (on numbers) applies.
-- i.e. P(0) ∧ (∀n, P(n) → P(succ n)) → ∀n, P(n).
-- Note: PureSet contains "non-numbers" (trees) too.
-- So we only prove this for "Valid Numerals".

/-- Predicate to check if a PureSet is a valid Von Neumann Ordinal -/
inductive IsOrdinal : PureSet → Prop
  | zero : IsOrdinal zero
  | succ {n} : IsOrdinal n → IsOrdinal (succ n)

theorem peano_induction (P : PureSet → Prop)
    (h0 : P zero)
    (hsucc : ∀ n, IsOrdinal n → P n → P (succ n)) :
    ∀ n, IsOrdinal n → P n := by
  intro n h_ord
  induction h_ord with
  | zero => exact h0
  | succ h_n ih =>
    apply hsucc
    exact h_n
    exact ih

end PhysicalLoF.SetTheory.Peano
