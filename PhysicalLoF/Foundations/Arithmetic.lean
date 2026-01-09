-- SPDX-License-Identifier: MIT
/-
  Arithmetic.lean
  ================
  Copyright (C) 2026 Tan Jun Liang <junliang9339@hotmail.com>
  Repository: https://github.com/poig/Lean-physical-laws-of-form

  Connecting Distinction to Arithmetic

  KEY INSIGHT:
  The Peano axioms are fundamentally about DISTINCTION:
  1. Zero is DISTINCT from all successors
  2. Successor is INJECTIVE (distinct inputs → distinct outputs)
  3. Induction uses CASE DISTINCTION (base vs step)

  This file proves that natural number arithmetic is grounded in distinction.
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Nat.Factors
import PhysicalLoF.Foundations.Distinction

namespace PhysicalLoF.Foundations

/-! ## Peano Axioms as Distinction -/

/--
  **PEANO AXIOM 1**: Zero is distinguished from all successors.

  This IS distinction: 0 ≠ Nat.succ n for all n.
-/
theorem peano_zero_distinct : ∀ n : ℕ, 0 ≠ Nat.succ n :=
  fun _ => Nat.noConfusion

/--
  **PEANO AXIOM 2**: Successor is injective.

  If Succ(m) = Succ(n), then m = n.
  Equivalently: m ≠ n → Succ(m) ≠ Succ(n)

  This preserves distinction through the successor operation.
-/
theorem peano_successor_injective : Function.Injective Nat.succ :=
  Nat.succ_injective

/--
  **PEANO AXIOM 3**: Induction uses case distinction.

  To prove P(n) for all n:
  - Base case: P(0) (distinguished from successors)
  - Inductive step: P(n) → P(n+1) (each n distinguished)
-/
theorem peano_induction_uses_distinction :
    ∀ (P : ℕ → Prop), P 0 → (∀ n, P n → P (n + 1)) → ∀ n, P n :=
  fun _ h0 hs n => Nat.recOn n h0 hs

/-! ## Arithmetic Derives from Distinction -/

/--
  **THE FUNDAMENTAL THEOREM OF ARITHMETIC DISTINCTION**:

  1+1=2 is not a tautology — it's PROVEN using distinction:
  - 1 = Succ(0)
  - 2 = Succ(Succ(0))
  - Addition is defined by distinguishing 0 from Succ(n)
-/
theorem one_plus_one : (1 : ℕ) + 1 = 2 := rfl

/--
  **ADDITION USES DISTINCTION**:

  The definition of addition pattern-matches on whether
  the second argument is 0 or Succ(b). This IS distinction!
-/
theorem addition_definition :
    -- Case 1: Adding zero (distinguished)
    (∀ a : ℕ, a + 0 = a) ∧
    -- Case 2: Adding successor (distinguished)
    (∀ a b : ℕ, a + Nat.succ b = Nat.succ (a + b)) :=
  ⟨Nat.add_zero, Nat.add_succ⟩

/--
  **MULTIPLICATION USES DISTINCTION**:

  Similarly, multiplication is defined by case distinction.
-/
theorem multiplication_definition :
    (∀ a : ℕ, a * 0 = 0) ∧
    (∀ a b : ℕ, a * Nat.succ b = a * b + a) :=
  ⟨Nat.mul_zero, Nat.mul_succ⟩

/-! ## Every Natural Number is Distinguishable -/

/--
  **ALL NATURALS ARE DISTINGUISHABLE**:

  Any two distinct natural numbers are distinguishable.
  This is because ℕ has decidable equality.
-/
theorem all_naturals_distinguishable : ∀ m n : ℕ, m = n ∨ m ≠ n :=
  fun m n => Classical.em (m = n)

/--
  **THE INTEGERS ARE TOTALLY ORDERED BY DISTINCTION**:

  For any m, n: either m < n, m = n, or m > n.
  This trichotomy IS triple distinction.
-/
theorem natural_trichotomy : ∀ m n : ℕ, m < n ∨ m = n ∨ m > n :=
  fun m n => Nat.lt_trichotomy m n

/-! ## Summary -/

/--
  **PEANO ARITHMETIC IS DISTINCTION-BASED**:

  All three Peano axioms derive from distinction:
  1. 0 ≠ Succ(n) — zero is distinguished
  2. Succ injective — distinction is preserved
  3. Induction — case distinction

  Therefore: Natural number arithmetic is grounded in distinction.
-/
theorem peano_is_distinction_based :
    -- Axiom 1: Zero is distinguished
    (∀ n, 0 ≠ Nat.succ n) ∧
    -- Axiom 2: Successor preserves distinction
    (∀ m n, Nat.succ m = Nat.succ n → m = n) ∧
    -- Bonus: All naturals are distinguishable
    (∀ m n : ℕ, m = n ∨ m ≠ n) := by
  refine ⟨?_, ?_, ?_⟩
  · exact fun _ => Nat.noConfusion
  · exact fun _ _ h => Nat.succ.inj h
  · exact fun m n => Classical.em (m = n)

/-! ## Prime Numbers as Irreducible Distinctions -/

/--
  **PRIMES ARE ATOMS OF ARITHMETIC**:

  A prime number is an "irreducible distinction" — it cannot be
  factored into smaller multiplicative parts.

  - Composite: 6 = 2 × 3 (CAN be distinguished further)
  - Prime: 7 = 7 (CANNOT be factored — atomic distinction!)

  This is the professional mathematical terminology:
  "Primes are the atoms of number theory" — they are irreducible elements.
-/
theorem prime_is_irreducible {p : ℕ} (hp : Nat.Prime p) :
    -- A prime cannot be factored into smaller parts
    ∀ a b : ℕ, p = a * b → a = 1 ∨ b = 1 := by
  intro a b hab
  have hdvd : a ∣ p := ⟨b, hab⟩
  have := hp.eq_one_or_self_of_dvd a hdvd
  rcases this with ha | ha
  · left; exact ha
  · right
    -- We know a = p, so b must be 1
    rw [ha] at hab
    nth_rewrite 1 [← Nat.mul_one p] at hab
    -- hab: p * 1 = p * b
    exact (Nat.eq_of_mul_eq_mul_left hp.pos hab).symm

/--
  **FUNDAMENTAL THEOREM OF ARITHMETIC** (Using Mathlib):

  Every number ≠ 0 has a prime factorization.
  Mathlib provides `Nat.primeFactorsList` which gives the factorization.

  This means: every composite distinction can be traced back to
  a unique set of "primitive distinctions" (primes).

  Primes are to NUMBERS what DISTINCTION is to CONCEPTS:
  the irreducible foundation!
-/
theorem fundamental_theorem_of_arithmetic (n : ℕ) (hn : n ≠ 0) :
    -- n equals the product of its prime factors
    n = (Nat.primeFactorsList n).prod ∧
    -- All factors are prime (using Nat.Prime)
    (∀ p ∈ Nat.primeFactorsList n, Nat.Prime p) :=
  ⟨(Nat.prod_primeFactorsList hn).symm,
   fun _ h => Nat.prime_of_mem_primeFactorsList h⟩

/--
  **PRIME DISTINCTION PROPERTY**:

  If a prime divides a product, it must divide one of the factors.
  This is the DEFINITION of prime in abstract algebra.

  p | (a × b) → (p | a) ∨ (p | b)
-/
theorem prime_divides_product {p a b : ℕ} (hp : Nat.Prime p) :
    p ∣ a * b → p ∣ a ∨ p ∣ b :=
  hp.dvd_mul.mp

/--
  **PRIMES ARE DISTINGUISHED FROM COMPOSITES**:

  The set of primes is distinguished from the set of composites.
  This is the most fundamental distinction in number theory.
-/
theorem prime_composite_distinction (n : ℕ) (hn : n > 1) :
    (Nat.Prime n) ∨ (∃ a b, a > 1 ∧ b > 1 ∧ n = a * b) := by
  by_cases hp : Nat.Prime n
  · left; exact hp
  · right
    -- n is composite, so minFac is a proper factor
    have hn1 : n ≠ 1 := Nat.ne_of_gt hn
    have hminPrime : Nat.Prime n.minFac := Nat.minFac_prime hn1
    have hdiv : n.minFac ∣ n := Nat.minFac_dvd n
    use n.minFac, n / n.minFac
    constructor
    · exact hminPrime.one_lt
    constructor
    · -- Prove n is not prime means minFac < n
      have hlt : n.minFac < n := by
        by_contra hge
        push_neg at hge
        -- hge : n ≤ n.minFac
        have n_pos : 0 < n := Nat.zero_lt_of_lt hn
        have minFac_le_n : n.minFac ≤ n := Nat.minFac_le n_pos
        have heq : n.minFac = n := Nat.le_antisymm minFac_le_n hge
        rw [heq] at hminPrime
        exact hp hminPrime
      -- Prove n / minFac > 1 using division properties
      have hdiv_pos : 0 < n / n.minFac := Nat.div_pos (Nat.le_of_dvd (Nat.zero_lt_of_lt hn) hdiv) hminPrime.pos
      have hne1 : n / n.minFac ≠ 1 := by
        intro heq
        have := Nat.div_mul_cancel hdiv
        rw [heq, Nat.one_mul] at this
        rw [this] at hlt
        exact Nat.lt_irrefl n hlt
      omega
    · -- Multiplication is commutative
      rw [Nat.mul_comm]
      exact (Nat.div_mul_cancel hdiv).symm

end PhysicalLoF.Foundations
