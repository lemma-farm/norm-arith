module
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.v7a74cf932f44.PDEFoundation.Measure.LpSpace
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.v7a74cf932f44.PDEFoundation.Sobolev.W1p.Basic
public import Mathlib
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Euclidean-gradient `L^p` representatives

The native gradient carrier `PDE.Vec d` has the finite-product supremum norm.
For Sobolev estimates, the gradient magnitude is instead the explicit
Euclidean norm `PDE.vecEuclideanNorm`.  This file transports native vector
fields to the internal Hilbert carrier and records the exact, factor-free
norm and `L^p` membership identities.

The coordinatewise predicate `PDE.GradMemLpOn` remains the compatibility
surface for existing developments.  Its equivalence with Hilbert-vector
`L^p` membership is exact and holds for every exponent.
-/
@[expose] public section
open scoped ENNReal
noncomputable section
namespace PDE
open MeasureTheory
/-- Reinterpret a native vector field in the internal Euclidean Hilbert
carrier. -/
def toHilbertVecField {d : ℕ} (F : Vec d → Vec d) :
    Vec d → HilbertVec d :=
  fun x => (F x).toHilbertVec
@[simp]
theorem toHilbertVecField_apply {d : ℕ} (F : Vec d → Vec d)
    (x : Vec d) :
    toHilbertVecField F x = (F x).toHilbertVec :=
  rfl
theorem gradMemLpOn_iff_memLp_toHilbertVecField
    {d : ℕ} {U : Set (Vec d)} {p : ℝ≥0∞}
    {Du : Vec d → Vec d} :
    GradMemLpOn U p Du ↔
      MemLp (toHilbertVecField Du) p (volumeOn U) := by
  simpa only [GradMemLpOn, MemLpOn, toHilbertVecField,
    Vec.toHilbertVec_apply] using
    (memLp_piLp_iff
      (f := toHilbertVecField Du)
      (p := p) (μ := volumeOn U)).symm
namespace MemLpOn
/-- Promote a scalar representative on `U` to its quotient `L^p(U)` class. -/
def toScalarLp {d : ℕ} {U : Set (Vec d)} {p : ℝ≥0∞}
    {u : Vec d → ℝ} (hu : MemLpOn U p u) :
    ScalarLp U p :=
  hu.toLp u
/-- The scalar quotient class agrees almost everywhere with the representative
used to construct it. -/
theorem coeFn_toScalarLp {d : ℕ} {U : Set (Vec d)} {p : ℝ≥0∞}
    {u : Vec d → ℝ} (hu : MemLpOn U p u) :
    ⇑hu.toScalarLp =ᵐ[volumeOn U] u :=
  hu.coeFn_toLp
end MemLpOn
namespace GradMemLpOn
def toHilbertVectorLp {d : ℕ} {U : Set (Vec d)} {p : ℝ≥0∞}
    {Du : Vec d → Vec d} (hDu : GradMemLpOn U p Du) :
    HilbertVectorLp U p :=
  (gradMemLpOn_iff_memLp_toHilbertVecField.mp hDu).toLp
    (toHilbertVecField Du)
/-- The Hilbert-vector quotient class agrees almost everywhere with the
lifted native gradient used to construct it. -/
theorem coeFn_toHilbertVectorLp
    {d : ℕ} {U : Set (Vec d)} {p : ℝ≥0∞}
    {Du : Vec d → Vec d} (hDu : GradMemLpOn U p Du) :
    ⇑hDu.toHilbertVectorLp =ᵐ[volumeOn U] toHilbertVecField Du :=
  (gradMemLpOn_iff_memLp_toHilbertVecField.mp hDu).coeFn_toLp
/-- Coordinatewise form of
`PDE.GradMemLpOn.coeFn_toHilbertVectorLp`. -/
theorem coeFn_toHilbertVectorLp_apply
    {d : ℕ} {U : Set (Vec d)} {p : ℝ≥0∞}
    {Du : Vec d → Vec d} (hDu : GradMemLpOn U p Du)
    (i : Fin d) :
    (fun x => hDu.toHilbertVectorLp x i) =ᵐ[volumeOn U]
      fun x => Du x i := by
  filter_upwards [hDu.coeFn_toHilbertVectorLp] with x hx
  exact congrArg (fun y : HilbertVec d => y i) hx
end GradMemLpOn
end PDE
