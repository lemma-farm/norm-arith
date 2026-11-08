module
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.vb7705ee35f51.HypoellipticAleksandrov.KineticAleksandrov.Holder.AdmissibilityMinimum
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.vb7705ee35f51.HypoellipticAleksandrov.KineticAleksandrov.Holder.Cap
import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.vb7705ee35f51.HypoellipticAleksandrov.KineticAleksandrov.Maximum.BorelSource
public import Mathlib.Analysis.Matrix.MeasurableSpace
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Topology.Separation.Regular
import Mathlib.Tactic
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Smooth interior cutoff for the nearly full superlevel estimate

The cutoff is constructed in the existing product coordinates. Its compact support
lies in the literal kinetic cylinder, and it equals one on the closed source cap.
-/
@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Holder
open Set MeasureTheory
open scoped MatrixOrder
end HypoellipticAleksandrov.KineticAleksandrov.Holder
