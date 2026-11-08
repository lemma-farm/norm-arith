module
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.v1cf492fae15a.PDEFoundation.Ambient.EuclideanNorm
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.v1cf492fae15a.PDEFoundation.Geometry.EuclideanBall
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Ambient Euclidean geometry

`PDE.Vec d` inherits the finite-product supremum norm and its associated
metric. That inherited norm and metric cannot be used as the manuscript's
round Euclidean geometry; this module instead exposes the sibling project's
explicit Euclidean dot product, norm, balls, closed balls, and spheres.
-/
@[expose] public section
