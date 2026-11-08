-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Pressure.PkBoundsP7SolutionBound
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Pressure.PkBoundsUnconditionalP8
set_option autoImplicit false
set_option warningAsError true
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic
set_option autoImplicit false
noncomputable section
namespace CKN
/-! The two cylinder bounds for the force terms `p₇` and `p₈` are added into a
single `L^{3/2}` bound on the parabolic cylinder.  This is the estimate
`r^{-2} ∬_{Q_r} |p₇ + p₈|^{3/2} ≤ (C₁₃(q) κ λ(z₀,ρ))^{3/2}` appearing in the
proof of `prop:lin34`(ii-b) of `paper/ckn.tex`. -/
end CKN
