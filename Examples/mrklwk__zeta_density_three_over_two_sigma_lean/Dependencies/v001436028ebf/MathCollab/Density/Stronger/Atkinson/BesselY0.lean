module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. Selected proofs adapted from DFIBesselKernel.lean,
exact source revision 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1,
released under MIT-0. See third_party/twelfth/NEUMANN_NATIVE_MANIFEST.json and third_party/twelfth/LICENSE-MIT-0.
Mathlib dependencies retain their Apache-2.0 attribution.
The literal classical Bessel kernel, principal half-power branches and
actual convergent integrals are preserved; no asymptotic bound is assumed.
-/
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY
open Complex Set MeasureTheory
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.Atkinson
/-- The exponentially decaying term in Schläfli's real integral
representation of the order-zero Neumann kernel. -/
noncomputable def dfiBesselY0Tail (x : ℝ) : ℝ :=
  ∫ t in Set.Ioi (0 : ℝ),
    Real.exp (-x * t) / Real.sqrt (1 + t ^ 2)
/-- The oscillatory term in Schläfli's representation, written after the
change of variables `u = π/2 - θ`.  Taking the imaginary part packages the
real sine integral while retaining the complex exponential needed for the
first-derivative estimate. -/
noncomputable def dfiBesselY0Osc (x : ℝ) : ℝ :=
  (∫ u in (0 : ℝ)..Real.pi / 2,
    Complex.exp (Complex.I * (x * Real.cos u))).im
/-- DFI's order-zero Neumann kernel, defined by the DLMF/Schläfli integral
representation
`Y₀(x) = (2/π) ( ∫₀^π/² sin(x cos u) du
                         - ∫₀^∞ exp(-xt)/sqrt(1+t²) dt )`.
The representation is used only for positive arguments, exactly as in DFI
Proposition 1. -/
noncomputable def dfiBesselY0 (x : ℝ) : ℝ :=
  (2 / Real.pi) * (dfiBesselY0Osc x - dfiBesselY0Tail x)
end MathCollab.Density.Stronger.Atkinson
