module
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.v7a74cf932f44.PDEFoundation.Ambient.EuclideanNorm
public import Mathlib
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Internal Hilbert realization of native vectors

Functional-analytic constructions sometimes need the Euclidean norm as the
typeclass norm. This file provides an internal `PiLp 2` realization together
with exact conversions to the native carrier `PDE.Vec`.

The native carrier remains the public ambient-space API. The wrapper in this
file is used only behind the conversion and norm identities below.
-/
@[expose] public section
namespace PDE
/-- Internal Hilbert realization of a native `d`-vector. -/
abbrev HilbertVec (d : ℕ) :=
  PiLp 2 (fun _ : Fin d => ℝ)
/-- Put a native vector into the internal Hilbert realization. -/
def Vec.toHilbertVec {d : ℕ} (x : Vec d) : HilbertVec d :=
  WithLp.toLp 2 x
@[simp]
theorem Vec.toHilbertVec_apply {d : ℕ} (x : Vec d) (i : Fin d) :
    x.toHilbertVec i = x i :=
  rfl
end PDE
