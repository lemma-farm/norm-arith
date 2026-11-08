-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.vd20c8d1f409f.CKN.Foundation.Ambient.Euclidean
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.vd20c8d1f409f.CKN.Foundation.Sobolev.Cutoff.Ball
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.vd20c8d1f409f.CKN.Foundation.Sobolev.Mollify.Basic
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Analysis.Normed.Lp.PiLp
set_option autoImplicit false
set_option warningAsError true
/-!
# A smooth ball cut-off with two derivative bounds

The native carrier is `Fin 3 → ℝ`.  The cut-off below is obtained by
convolving the indicator of the `7ρ/10` ball with a normalized smooth bump.
The bump is chosen with a slightly smaller inherited-metric radius so that
its Euclidean support has a strict collar in the native carrier.  This keeps
the stated Euclidean radii literal while avoiding an implicit change of norm.
-/
open Set MeasureTheory Metric
open scoped Convolution
set_option autoImplicit false
noncomputable section
namespace CKN
end CKN
