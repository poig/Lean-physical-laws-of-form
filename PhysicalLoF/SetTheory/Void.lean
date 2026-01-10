-- SPDX-License-Identifier: MIT
/-
  Void.lean
  =========
  The Void is the primary form.
-/

import PhysicalLoF.SetTheory.Base

namespace PhysicalLoF.SetTheory
open PureSet

/-- The Void is the set of nothing. -/
def TheVoid : PureSet := zero

/-- The Singleton (Primary Distinction). -/
def TheSingleton : PureSet := PureSet.singleton TheVoid

/-- Proof that The Void and The Singleton are Distinct. -/
theorem void_ne_singleton : TheVoid ≠ TheSingleton := by
  intro h
  unfold TheVoid TheSingleton zero PureSet.singleton at h
  contradiction

/-- The Mark creates a singleton. mark(x) = {x} -/
def mark (s : PureSet) : PureSet := PureSet.singleton s

/-- Distinction Principle: x ≠ {x} -/
theorem mark_creates_distinction (s : PureSet) : s ≠ mark s := by
  intro h
  unfold mark PureSet.singleton at h
  induction s with
  | void =>
    contradiction
  | set xs ih =>
    injection h with h_list
    -- xs = [set xs]
    have h_len : xs.length = [PureSet.set xs].length := by
      rw [h_list]
    -- But xs contains (set xs), so length xs >= length (set xs) > length xs ???
    -- Simpler: Structural inequality.
    -- sizeOf s < sizeOf {s} is guaranteed by Lean.
    have h_size : sizeOf xs = sizeOf [PureSet.set xs] := by
       rw [h_list]
    dsimp at h_size
    -- sizeOf [x] = 1 + sizeOf x
    -- sizeOf xs = 1 + sizeOf (set xs)
    -- sizeOf (set xs) = 1 + sizeOf xs
    -- So sizeOf xs = 1 + (1 + sizeOf xs)
    -- sizeOf xs = 2 + sizeOf xs -> False
    omega

end PhysicalLoF.SetTheory
