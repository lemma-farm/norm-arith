module
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.v4b3d3bae2d41.HypoellipticAleksandrov.Parabolic.LocalClassical
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Closure of local lower ellipticity

This module records that lower Loewner ellipticity is closed under limits of
continuous coefficient fields.  It is deliberately pointwise: no openness,
compactness, or positive ellipticity constant is needed for this extension.
-/
@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.Parabolic
open Matrix Set
open scoped MatrixOrder
namespace HasLowerEllipticityOn
end HasLowerEllipticityOn
end HypoellipticAleksandrov.Parabolic
