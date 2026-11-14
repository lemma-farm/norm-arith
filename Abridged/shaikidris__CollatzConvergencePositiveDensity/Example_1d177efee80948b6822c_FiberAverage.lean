module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Probability.ProbabilityMassFunction.Constructions
public import Mathlib.Data.PNat.Basic
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Data.Rat.Lemmas
public import Mathlib.Tactic.Ring
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Logic.Function.Iterate
public import Mathlib.Tactic.Linarith
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.LinearCombination
public import Mathlib.RingTheory.Nilpotent.Basic
public import Mathlib.GroupTheory.Index

-- ==== Examples.shaikidris__CollatzConvergencePositiveDensity.Dependencies.v691c2db515c3.WordCertDensity.Reference.Residues ====
public section
/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik

The binary-unit projection argument is adapted from Lech Mazur,
Copyright 2026 Lech Mazur, under Apache License 2.0. The source LICENSE and
NOTICE are retained at research/sources/mazur_830b9d3f38f2/.
The recursive offsets use the local word algebra and reversed numerator.
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
/-!
# Dyadic offsets in ternary residue groups

Binary denominators are units modulo every power of three, including the
one-point group at level zero. A recursive residue offset is connected to the
rational inverse offset by their common integral numerator and binary denominator.
No generic rational cast into a ternary residue ring is used.
-/
@[expose] public section
namespace WordCertDensity
namespace Reference
noncomputable def project {m n : ℕ} (h : m ≤ n) :
    ZMod (3 ^ n) →+* ZMod (3 ^ m) :=
  ZMod.castHom (Nat.pow_dvd_pow 3 h) (ZMod (3 ^ m))
end Reference
namespace ValuationWord
end ValuationWord
end WordCertDensity

end
end

-- ==== Examples.shaikidris__CollatzConvergencePositiveDensity.Dependencies.v691c2db515c3.WordCertDensity.Reference.Projectivity ====
public section
/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik

The PMF projection and real-sum bridge follow the short map-composition
arguments of Lech Mazur, Copyright 2026 Lech Mazur, under Apache License 2.0.
The source LICENSE and NOTICE are retained at
research/sources/mazur_830b9d3f38f2/. The finite normalization proofs are local.
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
/-!
# Projectivity and full-group normalization

The geometric reference law projects exactly between ternary levels.
Counting each projection fiber gives the density average identity and the
uniform lifting of probability masses. The L1 identities contain no factor
one half, and the marker factor two thirds is paid once.
-/
@[expose] public section
namespace WordCertDensity
namespace Reference
noncomputable def fiber {m n : ℕ} (h : m ≤ n) (y : ZMod (3 ^ m)) : Finset (ZMod (3 ^ n)) :=
  Finset.univ.filter (fun x => project h x = y)
end Reference
end WordCertDensity

end
end

-- ==== Examples.shaikidris__CollatzConvergencePositiveDensity.Examples.Example_1d177efee80948b6822c_FiberAverage ====
/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik

Finite fiber/Fourier arguments adapted from Lech Mazur, Copyright 2026 Lech Mazur,
under Apache License 2.0. The original LICENSE and NOTICE are retained at
research/sources/mazur_830b9d3f38f2/. This version uses the actual local projection,
explicit Mathlib imports and the pinned module format.
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
/-!
# The actual ternary fiber average

The operator divides the sum on the actual projection fiber by its cardinality.
It preserves mass, is positive and contracts the unhalved finite L1 norm.
The reference-law specialization agrees with the existing density oscillation.
-/
@[expose] public section
namespace WordCertDensity
namespace FiniteFourier
open Reference
/-- Average a real vector on its actual ternary projection fiber. -/
noncomputable def fiberAverage {m n : ℕ} (h : m ≤ n)
    (p : ZMod (3 ^ n) → ℝ) (x : ZMod (3 ^ n)) : ℝ :=
  (∑ y ∈ fiber h (project h x), p y) / (3 : ℝ) ^ (n - m)

noncomputable def oscillation {m n : ℕ} (h : m ≤ n) (p : ZMod (3 ^ n) → ℝ) : ℝ :=
  ∑ x, |p x - fiberAverage h p x|
set_option linter.unusedVariables false in
theorem oscillation_add_le {m n : ℕ} (h : m ≤ n) (p q : ZMod (3 ^ n) → ℝ) 
    (h_WordCertDensity_FiniteFourier_fiberAverage_add : ∀ {m n : ℕ} (h : m ≤ n) (p q : ZMod (3 ^ n) → ℝ) (x : ZMod (3 ^ n)),
      WordCertDensity.FiniteFourier.fiberAverage h (fun (y : ZMod (3 ^ n)) ↦ p y + q y) x =
        WordCertDensity.FiniteFourier.fiberAverage h p x +
          WordCertDensity.FiniteFourier.fiberAverage h q x)
    :
    oscillation h (fun x => p x + q x) ≤ oscillation h p + oscillation h q := by
  simp only [oscillation, h_WordCertDensity_FiniteFourier_fiberAverage_add, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro x _
  rw [show p x + q x - (fiberAverage h p x + fiberAverage h q x) =
    (p x - fiberAverage h p x) + (q x - fiberAverage h q x) by ring]
  exact abs_add_le _ _
end FiniteFourier
end WordCertDensity
