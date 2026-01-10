-- SPDX-License-Identifier: MIT
/-
  Base.lean
  =========
  The Foundational Inductive Type for our Set Theory.
  We use Hereditarily Finite Sets (Pure Sets) codified via Lists.
-/

namespace PhysicalLoF.SetTheory

/--
  PureSet represents a set that contains only other sets.
  This allows us to model the Cumulative Hierarchy (V).

  We uses `List` for the internal representation to keep it constructive,
  but conceptually order is ignored.
-/
inductive PureSet : Type
  | void : PureSet
  | set  : List PureSet → PureSet
  deriving Repr, Inhabited

namespace PureSet

-- Manual DecidableEq instance might be needed if deriving fails,
-- but for now we will skip it to fix the immediate build error.
-- We can reason about equality via standard propositional equality.

/-- The empty set (0) -/
def zero : PureSet := void

/-- Singleton set {x} -/
def singleton (x : PureSet) : PureSet := set [x]

end PureSet
end PhysicalLoF.SetTheory
