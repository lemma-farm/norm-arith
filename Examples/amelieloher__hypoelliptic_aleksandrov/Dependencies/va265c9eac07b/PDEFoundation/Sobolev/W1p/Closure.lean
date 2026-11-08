module
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.va265c9eac07b.PDEFoundation.Measure.FiniteVectorConvergence
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.va265c9eac07b.PDEFoundation.Sobolev.W1p.RepresentativeGraph
public import Mathlib
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Closure of representative weak gradients under `L^p` convergence

This file exposes the closed-graph limit principle behind Sobolev
composition and truncation arguments.  If values and every native gradient
coordinate converge in `L^p`, then a limit of weak-gradient pairs is again a
weak-gradient pair.

The proof passes through the quotient `L^p` closed graph.  The native gradient
is lifted internally to `HilbertVec`; the public assumptions and conclusion
remain on `Vec d`, and coordinatewise convergence is converted to the exact
Euclidean-gradient norm without a dimension-dependent loss.
-/
@[expose] public section
open scoped ENNReal Topology
namespace PDE
open Filter MeasureTheory
end PDE
