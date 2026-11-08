-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v09f1d5c1ae75.CKN.Core.Step3.LocalEquationRepresentation
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v09f1d5c1ae75.CKN.Foundation.Heat.BackwardPotentialKernelBridge
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v09f1d5c1ae75.CKN.Foundation.Sobolev.Cutoff.SpaceTime
set_option autoImplicit false
set_option warningAsError true
open scoped BigOperators ENNReal NNReal Topology
open MeasureTheory MeasureTheory.Measure Set Metric
set_option autoImplicit false
noncomputable section
namespace CKN.Core.Step3
open CKN.Foundation.Heat CKN.Foundation.Parabolic
open CKN.Core.HeatPotential
structure DuhamelSupportData
    (v g : ParabolicPoint → Vec3)
    (h : Fin 3 → ParabolicPoint → Vec3) where
  r : ℝ
  R : ℝ
  t₀ : ℝ
  hr : 0 ≤ r
  hrR : r < R
  v_support : ∀ i : Fin 3, ∀ z ∈ tsupport (fun w => v w i),
    z.1 ∈ euclideanBall (0 : Vec3) r ∧ z.2 ∈ Ioo (t₀ - r ^ 2) t₀
  g_support : ∀ i : Fin 3, ∀ z ∈ tsupport (fun w => g w i),
    z.1 ∈ euclideanBall (0 : Vec3) r ∧ z.2 ∈ Ioo (t₀ - r ^ 2) t₀
  h_support : ∀ j i : Fin 3, ∀ z ∈ tsupport (fun w => h j w i),
    z.1 ∈ euclideanBall (0 : Vec3) r ∧ z.2 ∈ Ioo (t₀ - r ^ 2) t₀
end CKN.Core.Step3
