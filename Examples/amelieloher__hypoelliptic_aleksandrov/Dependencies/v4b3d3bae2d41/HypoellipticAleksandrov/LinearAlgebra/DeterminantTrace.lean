module
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.v4b3d3bae2d41.HypoellipticAleksandrov.Ambient.Basic
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Analysis.MeanInequalities
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Determinant--trace inequalities

This module proves the finite-dimensional determinant--trace estimate used in
the smooth parabolic ABP argument.  It is purely matrix algebra: no
ellipticity predicate or PDE estimate appears here.
-/
@[expose] public section
open scoped BigOperators MatrixOrder
open Matrix
namespace HypoellipticAleksandrov
end HypoellipticAleksandrov
