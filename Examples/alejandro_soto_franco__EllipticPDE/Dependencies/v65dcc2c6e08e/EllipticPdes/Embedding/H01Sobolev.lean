/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/
module
public import Examples.alejandro_soto_franco__EllipticPDE.Dependencies.v65dcc2c6e08e.EllipticPdes.Sobolev.Basic
public import Examples.alejandro_soto_franco__EllipticPDE.Dependencies.v65dcc2c6e08e.EllipticPdes.Embedding.Morrey
public import Mathlib.Analysis.FunctionalSpaces.SobolevInequality
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# Sobolev embedding of `H₀¹(Ω)`

The Gagliardo-Nirenberg-Sobolev inequality `‖u‖_{L^{2⋆}} ≤ C ‖∇u‖_{L²}`, with `2⋆` the Sobolev
conjugate `1/2⋆ = 1/2 - 1/d`, is Mathlib's
`MeasureTheory.eLpNorm_le_eLpNorm_fderiv_of_eq` for a smooth compactly supported function. This
file passes it from the test functions to their closure `H₀¹(Ω)` and bundles the result as a
continuous linear map.

## Lower semicontinuity in place of continuity

`EllipticPdes.Poincare.poincare_H01` extends the Poincaré inequality to `H₀¹(Ω)` by observing that
the estimate is a closed condition on a continuous function of the graph. That argument is
unavailable here: the two sides of the Sobolev estimate live at different exponents, and the
`L^q` seminorm of the function coordinate is not a continuous function of the `H¹` graph.

What survives is lower semicontinuity. Convergence in `H¹` gives convergence of the function
coordinate in `L²(Ω)`, hence convergence in measure, and
`MeasureTheory.eLpNorm_le_of_tendstoInMeasure` passes an eventual bound at the exponent `q` to the
limit through Fatou's lemma. The bound along the sequence is not constant, so it is the limit of
the right-hand sides that is used, one strict upper bound at a time.

The transfer takes the test-function estimate as a hypothesis at an arbitrary exponent and an
arbitrary constant, in the manner of `EllipticPdes.Poincare.poincare_H01`, so each
Gagliardo-Nirenberg-Sobolev variant proved for test functions reaches `H₀¹(Ω)` by supplying it.
Two are supplied: the critical exponent on any `Ω`, and every exponent below it on a bounded `Ω`.

## Main declarations

* `EllipticPdes.Embedding.eLpNorm_testGraph_le`: the estimate on a test function at the critical
  exponent, read off the graph coordinates.
* `EllipticPdes.Embedding.eLpNorm_testGraph_le_of_isBounded`: the same at every exponent below the
  critical one, on a bounded domain.
* `EllipticPdes.Embedding.eLpNorm_le_of_mem_H01_of_forall_testFn`: the transfer principle, from an
  estimate on test functions to the same estimate on `H₀¹(Ω)`.
* `EllipticPdes.Embedding.eLpNorm_le_of_mem_H01` and
  `EllipticPdes.Embedding.eLpNorm_le_of_mem_H01_of_isBounded`: the two estimates on `H₀¹(Ω)`.
* `EllipticPdes.Embedding.sobolevEmbL`: the embedding `H₀¹(Ω) →L[ℝ] L^q(Ω)` built from such an
  estimate, with `EllipticPdes.Embedding.coeFn_sobolevEmbL` identifying it with the function
  coordinate and `EllipticPdes.Embedding.norm_sobolevEmbL_le` bounding it by the gradient alone.

## References

L. C. Evans, *Partial Differential Equations* (2nd ed.), §5.6.1, Theorem 1; H. Brezis,
*Functional Analysis, Sobolev Spaces and Partial Differential Equations*, Corollary 9.9.
-/
@[expose] public section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace EllipticPdes.Embedding
open EllipticPdes.Sobolev
variable {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))} {p' : ℝ≥0}
section Bundled
variable {q : ℝ≥0∞} [Fact (1 ≤ q)] {C : ℝ≥0}
end Bundled
end EllipticPdes.Embedding
