/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik

The PMF projection and real-sum bridge follow the short map-composition
arguments of Lech Mazur, Copyright 2026 Lech Mazur, under Apache License 2.0.
The source LICENSE and NOTICE are retained at
research/sources/mazur_830b9d3f38f2/. The finite normalization proofs are local.
-/
module
public import Examples.shaikidris__CollatzConvergencePositiveDensity.Dependencies.v691c2db515c3.WordCertDensity.Reference.Law
import Mathlib.GroupTheory.Index
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
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
