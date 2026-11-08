module
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.vf33f9f71f919.HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer.Series
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.vf33f9f71f919.HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer.IntegralKernel
import Mathlib.Tactic.Linarith
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Positive integral definitions of Kummer U

`UI` has positive shape and argument. `UN` is the source transformation for the
negative shape interval. The real auxiliary formulae are only characterized at positive
arguments; their values outside that domain are never used as special-function values.
-/
@[expose] public noncomputable section
open Set MeasureTheory
namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer
/-- The Laplace kernel with positive first parameter. -/
def laplaceKernel (a : Pos) (b z t : ℝ) : ℝ := laplaceKernelReal a.1 b z t
def UIr (a : Pos) (b z : ℝ) : ℝ :=
  (Real.Gamma a.1)⁻¹ * ∫ t in Ioi (0 : ℝ), laplaceKernel a b z t
theorem integrable_laplaceKernel (a : Pos) (b z : ℝ) (hz : 0 < z) :
    IntegrableOn (laplaceKernel a b z) (Ioi 0) volume :=
  integrableOn_laplaceKernelReal a.1 b z a.2 hz
end HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer
