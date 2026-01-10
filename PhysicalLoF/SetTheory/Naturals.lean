-- SPDX-License-Identifier: MIT
/-
  Naturals.lean
  =============
  Deriving Number from Distinction.

  We use the Von Neumann construction:
  0 := ∅
  n+1 := n ∪ {n}
-/

import PhysicalLoF.SetTheory.Base

namespace PhysicalLoF.SetTheory
open PureSet

/-- Singleton set {x} -/
def singleton (x : PureSet) : PureSet := PureSet.set [x]

/-- Union of x and {x} (Successor) -/
def succ (n : PureSet) : PureSet :=
  match n with
  | void => PureSet.set [void]          -- 0 -> {0}
  | PureSet.set xs => PureSet.set (n :: xs)     -- {a...} -> {n, a...}

/-- The Standard Numbers -/
def one   : PureSet := succ zero
def two   : PureSet := succ one
def three : PureSet := succ two

/-! ## Proving They Are Distinct -/

/-- 0 ≠ 1 -/
theorem zero_ne_one : zero ≠ one := by
  intro h
  -- one = succ zero = set [void]
  unfold one succ zero at h
  -- void = set [void]
  contradiction

/-- 1 ≠ 2 -/
theorem one_ne_two : one ≠ two := by
  intro h
  -- one is set [void]
  have h1 : one = PureSet.set [void] := rfl
  -- two is set [one, void]
  have h2 : two = PureSet.set [one, void] := rfl

  rw [h1, h2] at h
  injection h with h_list

  -- We prove 1 = 2 implies False
  have h_len : ([void] : List PureSet).length = ([one, void] : List PureSet).length := by
    rw [h_list]

  simp at h_len
  -- 1 = 2
  contradiction

/-! ## The Bridge to Lean's Nat -/

/-- Converting our Von Neumann sets back to Lean Naturals -/
def toNat : PureSet → Nat
  | void => 0
  | PureSet.set xs => xs.length

/-- A precise structural isomorphism generator -/
def fromNat : Nat → PureSet
  | 0 => zero
  | n + 1 => succ (fromNat n)

theorem fromNat_zero : fromNat 0 = zero := rfl
theorem fromNat_one  : fromNat 1 = one  := rfl
theorem fromNat_two  : fromNat 2 = two  := rfl

end PhysicalLoF.SetTheory
