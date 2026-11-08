module
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.v6f38647c1638.HypoellipticAleksandrov.KineticAleksandrov.Bellman.GaussianKernelCalculus
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Measure.Comap
public import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! # Literal time-integrated Kolmogorov measure

The time and plane measures are pullbacks along the open-subtype embeddings. No value of
an integrand at nonpositive time and no assumed fundamental-solution existence is used.
-/
@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open MeasureTheory Set
end HypoellipticAleksandrov.KineticAleksandrov
