-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v2e00e306ea72.CKN.Foundation.Sobolev.WeakDerivative
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Convolution
set_option autoImplicit false
set_option warningAsError true
/-!
# ContDiffBump mollification

Adapted from PDEFoundation (EllipticRegularity, 2026) with the author's
permission. The custom convex-approximation chain was not used here: Mathlib
v4.34 already provides normalized `ContDiffBump` kernels, convolution
regularity, and approximate-identity convergence. This direct port keeps the
kernel and convolution API independent of the sibling geometry layer.
-/
open scoped Convolution Topology
namespace CKN
/-- A smooth bump centered at zero with outer radius `ε`. -/
noncomputable def standardMollifier {d : ℕ} (ε : ℝ) (hε : 0 < ε) :
    ContDiffBump (0 : Vec d) :=
  { rIn := ε / 2
    rOut := ε
    rIn_pos := half_pos hε
    rIn_lt_rOut := half_lt_self hε }
/-- The normalized scalar kernel associated with `standardMollifier`. -/
noncomputable def mollifier {d : ℕ} (ε : ℝ) (hε : 0 < ε) : Vec d → ℝ :=
  (standardMollifier ε hε).normed MeasureTheory.volume
theorem mollifier_hasCompactSupport {d : ℕ} {ε : ℝ} (hε : 0 < ε) :
    HasCompactSupport (mollifier (d := d) ε hε) := by
  exact (standardMollifier (d := d) ε hε).hasCompactSupport_normed
theorem mollifier_contDiff {d : ℕ} {ε : ℝ} (hε : 0 < ε) {n : ℕ∞} :
    ContDiff ℝ n (mollifier (d := d) ε hε) := by
  exact (standardMollifier (d := d) ε hε).contDiff_normed
noncomputable def mollify {d : ℕ} (u : Vec d → ℝ) (ε : ℝ) (hε : 0 < ε) :
    Vec d → ℝ :=
  MeasureTheory.convolution (mollifier (d := d) ε hε) u
    (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume
theorem mollify_contDiff {d : ℕ} {u : Vec d → ℝ} {ε : ℝ} (hε : 0 < ε)
    {n : ℕ∞} (hu : MeasureTheory.LocallyIntegrable u MeasureTheory.volume) :
    ContDiff ℝ n (mollify u ε hε) := by
  exact (mollifier_hasCompactSupport (d := d) hε).contDiff_convolution_left
    (L := ContinuousLinearMap.lsmul ℝ ℝ) (mollifier_contDiff (d := d) hε) hu
end CKN
