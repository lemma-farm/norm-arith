/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Examples.scottnarmstrong__MarkovProcess.Dependencies.v1421b971f7e5.MarkovProcess.Kernel.KernelSemigroup
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Intrinsic Kolmogorov moment bounds for a transition semigroup

Kolmogorov's continuity criterion is usually imposed on an already constructed coordinate
process.  This file states the same criterion directly on the transition semigroup: the
`p`-th moment of the displacement accumulated over a time step `h` is at most `M * h ^ q`,
uniformly in the starting point.

The predicate is purely a moment bound on the transition kernels.  It makes no path-space,
continuity, or stochastic-process claim; the transport of this bound to the canonical
dense-time coordinate process is proved elsewhere.
-/
open MeasureTheory
open scoped ENNReal NNReal
namespace MarkovProcess
namespace SubMarkovKernelSemigroup
variable {alpha : Type*} [PseudoEMetricSpace alpha] [MeasurableSpace alpha]
/-- A uniform `p`-th moment bound on the displacement of `P` over time `h`, of order `h ^ q`.

The exponents are constrained by `0 < p` and `1 < q`, exactly the range in which the
Kolmogorov--Chentsov threshold `(q - 1) / p` is a positive Hölder exponent.  The bound is demanded for every time `h ≥ 0`, not only
for small `h`; this is stronger than the local criterion the Kolmogorov--Chentsov theorem
needs, and it is what the bridge to `KolmogorovRegular` consumes. -/
def HasKolmogorovMoments (P : SubMarkovKernelSemigroup alpha) (p q : ℝ) (M : ℝ≥0) : Prop :=
  0 < p ∧ 1 < q ∧
    ∀ (h : ℝ≥0) (y : alpha), ∫⁻ z, edist z y ^ p ∂(P h y) ≤ M * (h : ℝ≥0∞) ^ q
namespace HasKolmogorovMoments
variable {P : SubMarkovKernelSemigroup alpha} {p q : ℝ} {M : ℝ≥0}
end HasKolmogorovMoments
end SubMarkovKernelSemigroup
end MarkovProcess
