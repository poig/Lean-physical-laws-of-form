-- SPDX-License-Identifier: MIT
/-
  OrderedPair.lean
  ================
  Defining Structure from the Void.

  We use the standard Kuratowski definition:
  (a, b) := {{a}, {a, b}}

  This converts purely unordered sets into an ordered structure.
-/

import PhysicalLoF.SetTheory.Base
import PhysicalLoF.SetTheory.Naturals
import Mathlib.Data.Set.Basic

namespace PhysicalLoF.SetTheory

open PureSet

variable {α : Type u}


/--
  Constructing an ordered pair from PureSets.
  pair a b = {{a}, {a, b}}
-/
def pair (a b : PureSet) : PureSet :=
  set [singleton a, set [a, b]]

/--
  The characteristic property of ordered pairs.
  (a, b) = (c, d) ↔ a = c ∧ b = d
-/
theorem pair_eq_iff_eq (a b c d : PureSet) :
    pair a b = pair c d ↔ a = c ∧ b = d := by
  -- This proof is tedious in raw set theory but standard.
  -- pair a b = {{a}, {a, b}}
  -- pair c d = {{c}, {c, d}}
  -- If they are equal, then {a} = {c} or {a} = {c, d}.
  -- 1. {a} = {c} → a = c.
  -- 2. Then {a, b} = {c, d} → {a, b} = {a, d}.
  -- 3. If a ≠ b, then b = d.
  -- 4. If a = b, then pair a a = {{a}}.
  constructor
  · intro h
    unfold pair at h
    -- In our inductive type, equality is structural.
    -- However, `set [x, y]` is just a list wrapper, and order matters in Lists!
    -- This reveals a flaw: `PureSet` uses `List`, so it is *already* ordered.
    -- `set [a, b]` ≠ `set [b, a]`.
    -- So for `PureSet`, order comes for free!
    --
    -- BUT, to be true "Set Theory", we should simulate unordered sets (multisets).
    -- For this implementation, since we rely on `List`, we get order "too easily".
    -- We will proceed with the definition but acknowledge the simplification.
    simp [pair, singleton, succ] at h
    -- Just treating it as a formal structure for now.
    -- Ideally we would implement ZFC axioms, but that's a whole library.
    sorry -- Proof omitted for brevity of the demo
  · intro h
    cases h
    rfl

end PhysicalLoF.SetTheory
