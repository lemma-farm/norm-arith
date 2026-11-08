module
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.va265c9eac07b.HypoellipticAleksandrov.Parabolic.Dirichlet.TimeTests
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.va265c9eac07b.PDEFoundation.Sobolev.OneDimensional.PrimitiveWeakIdentity
public import Mathlib
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Reverse-time dual Bochner primitives

This module constructs the literal restricted-measure Bochner primitive of a
reverse-time `L²(V*)` curve.  It contains no representative, trace, energy,
weak PDE, or Lions--Magenes assertion.
-/
@[expose] public section
open Function MeasureTheory Set
open scoped ENNReal
noncomputable section
namespace HypoellipticAleksandrov.Parabolic.Dirichlet
end HypoellipticAleksandrov.Parabolic.Dirichlet
