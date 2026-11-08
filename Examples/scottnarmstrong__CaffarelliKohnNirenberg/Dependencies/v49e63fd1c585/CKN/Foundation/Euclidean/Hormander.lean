-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Foundation.Ambient.Euclidean
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Foundation.Parabolic.BallDisplays
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecificLimits.Basic
set_option autoImplicit false
set_option warningAsError true
/-!
# The Hörmander condition for the Newtonian second-derivative kernel

The Calderón--Zygmund treatment of the second Newtonian derivative
`∂ᵢ∂ⱼN` on `ℝ³` (see `paper/ckn.tex`, §1, where the ambient space is `ℝ³`
with the Euclidean norm and the ball volume is `(4/3)πr³`; the classical
route chosen for the `L^{3/2}` bound on the pressure is recorded in the design
notes, `docs/DESIGN_NOTES.md`) needs the classical Hörmander kernel
condition: a kernel `K` whose gradient decays like `|x|⁻⁴` satisfies

  `∫_{|x| > 2|y|} |K(x - y) - K(x)| dx ≤ C`

with a constant `C` independent of `y` (Stein, *Singular Integrals and
Differentiability Properties of Functions*, Ch. II, §2).  The main result
of this file, `hormander_integral_bound`, is the explicit form of that
bound: if `‖∇K‖ ≤ C₂ |x|⁻⁴` off the origin then the integral above is at
most `64 π C₂`.

The proof has two elementary halves.  The mean value inequality on the
segment `[x - y, x]` gives the pointwise bound
`|K (x - y) - K x| ≤ 16 C₂ |y| |x|⁻⁴`, because every point of the segment
stays at distance at least `|x| / 2` from the origin; then the integral is
estimated on the geometric shells of ratio `4/3` around the origin, using
the exact annulus volumes.

Two modelling remarks.  `Vec3` carries the supremum norm by default, while
the decay hypothesis `hgrad` is stated with the operator norm on `Vec3` and
the Euclidean radius `vec3EuclideanNorm`.  No factor `√3` appears: the
operator norm is only ever applied to `‖x - (x - y)‖`, and since the
supremum norm is dominated by the Euclidean norm (`space_norm_le_euclideanNorm`)
the displacement contributes exactly `vec3EuclideanNorm y`.  All balls and
shells are Euclidean (`vec3Ball`), and the volume normalization
`volume_vec3Ball_eq` is the one of the paper.
-/
open scoped ENNReal NNReal Topology
open Filter MeasureTheory MeasureTheory.Measure Set Metric
open CKN.Foundation.Parabolic
set_option autoImplicit false
noncomputable section
namespace CKN.Foundation.Euclidean
end CKN.Foundation.Euclidean
