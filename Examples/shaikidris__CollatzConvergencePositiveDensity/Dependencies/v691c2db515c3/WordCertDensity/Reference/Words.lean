/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik

The iid list construction, atom and take/drop proofs are adapted from
Lech Mazur, Copyright 2026 Lech Mazur, under Apache License 2.0. The source
LICENSE and NOTICE are retained at research/sources/mazur_830b9d3f38f2/.
Modifications use the local geometric law and valuation-word totals.
-/
module
public import Examples.shaikidris__CollatzConvergencePositiveDensity.Dependencies.v691c2db515c3.WordCertDensity.Reference.Geometric
public import Examples.shaikidris__CollatzConvergencePositiveDensity.Dependencies.v691c2db515c3.WordCertDensity.Words.Algebra
import Mathlib.Tactic.NormNum
set_option autoImplicit false
set_option relaxedAutoImplicit false
/-!
# Independent geometric words

A word of the specified length has probability two to the negative total
valuation. The head and tail of a reference word are independent, expressed
as an equality of probability mass functions. No physical-source sampling
assumption is part of these identities.
-/
@[expose] public section
namespace WordCertDensity
namespace Reference
end Reference
end WordCertDensity
