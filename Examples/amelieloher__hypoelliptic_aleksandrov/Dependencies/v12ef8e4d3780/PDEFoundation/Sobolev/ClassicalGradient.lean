module
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.v12ef8e4d3780.PDEFoundation.Ambient.Basis
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.FDeriv.Basic
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Classical gradients in the native ambient space

The inherited norm on `PDE.Vec d` is the finite-product supremum norm. This
file packages the coordinate gradient of a classically differentiable scalar
function as a native vector and relates directional derivatives to the
explicit Euclidean dot product. Quantitative PDE estimates should use the
resulting Euclidean Cauchy--Schwarz inequality, not the operator norm induced
by the inherited product norm.
-/
@[expose] public section
namespace PDE
/-- The coordinate gradient of a scalar function, expressed in the native
vector carrier. -/
noncomputable def classicalGradient {d : ℕ}
    (f : Vec d → ℝ) (x : Vec d) : Vec d :=
  fun i => (fderiv ℝ f x) (basisVec i)
end PDE
