/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik

The positivity, oddness, factorization and ordinary-block proofs are adapted
from Lech Mazur, Copyright 2026 Lech Mazur, under the Apache License, Version 2.0.
Modifications use local dynamics interfaces and add the odd-quotient bridge.
The source LICENSE and NOTICE are retained at research/sources/mazur_830b9d3f38f2/.
-/
module
public import Examples.shaikidris__CollatzConvergencePositiveDensity.Dependencies.v691c2db515c3.WordCertDensity.Dynamics.Ordinary
public import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic.NormNum
set_option autoImplicit false
set_option relaxedAutoImplicit false
/-!
# Actual accelerated Collatz blocks

The exponent is the exact exponent of two in `3 * x + 1`. On odd inputs,
one accelerated step consists of one ordinary odd step and that many halvings.
The map is totalized on naturals; physical histories require positive odd inputs.
-/
@[expose] public section
namespace WordCertDensity
/-- Exact two-adic valuation of the numerator in an accelerated step. -/
def acceleratedExponent (x : ℕ) : ℕ := (3 * x + 1).factorization 2
/-- Divide the odd-step numerator by its full power of two. -/
def acceleratedStep (x : ℕ) : ℕ := (3 * x + 1) / 2 ^ acceleratedExponent x
/-- The chronological valuations along a finite accelerated orbit. -/
def acceleratedValuations (x depth : ℕ) : List ℕ :=
  (List.range depth).map fun j => acceleratedExponent ((acceleratedStep^[j]) x)
end WordCertDensity
