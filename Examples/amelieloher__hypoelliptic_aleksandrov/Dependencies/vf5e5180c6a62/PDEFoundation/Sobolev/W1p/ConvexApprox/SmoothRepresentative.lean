module
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.vf5e5180c6a62.PDEFoundation.Measure.Jensen
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.vf5e5180c6a62.PDEFoundation.Sobolev.W1p.Basic
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.vf5e5180c6a62.PDEFoundation.Sobolev.W1p.ConvexApprox.Kernel
public import Mathlib
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Smooth representatives for convex-domain approximation

This file defines the globally smooth representative of convex approximation.
It also records the measurable change of variables, exact `L^p` bounds, and
integrability lemmas needed by the later density and weak-derivative modules.

The convolution contraction used below is kept private: it is an implementation
lemma for this layer, not a second public Sobolev-space API.
-/
@[expose] public section
open scoped ENNReal Pointwise Convolution
namespace PDE
open MeasureTheory
noncomputable section
end
end PDE
