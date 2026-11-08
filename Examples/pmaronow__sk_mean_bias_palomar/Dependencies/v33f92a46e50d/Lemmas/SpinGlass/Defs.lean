module
/- Modified for this distribution (2026): Lean compiler/module compatibility and
   library interface adaptations. Existing source notices are retained. -/
public import Examples.pmaronow__sk_mean_bias_palomar.Dependencies.v33f92a46e50d.Lemmas.SpinGlass.Gaussian_IBP_Hilbert
public import Mathlib
public import Mathlib.Analysis.Calculus.FDeriv.WithLp
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
set_option autoImplicit true
set_option linter.deprecated false
@[expose] public section
open MeasureTheory ProbabilityTheory Real BigOperators Filter Topology
namespace SpinGlass
variable (N : ℕ) (β : ℝ)
/-! ### Basic Definitions -/
abbrev Config := Fin N → Bool
def spin (σ : Config N) (i : Fin N) : ℝ := if σ i then 1 else -1
abbrev EnergySpace := PiLp 2 (fun _ : Config N => ℝ)
/-- Magnetization of a configuration: \( \sum_{i=1}^N \sigma_i \) (with `σ_i ∈ {±1}`). -/
def magnetization (σ : Config N) : ℝ :=
  ∑ i : Fin N, spin N σ i
/--
External field energy term:
\[
H_{\text{field}}(\sigma) = h \sum_{i=1}^N \sigma_i.
\]

This is the physically correct “magnetic field” contribution (it depends on `σ`).
-/
def magnetic_field_vector (h : ℝ) : EnergySpace N :=
  WithLp.toLp 2 (fun σ : Config N => h * magnetization N σ)
noncomputable instance : InnerProductSpace ℝ (EnergySpace N) :=
  PiLp.innerProductSpace (𝕜 := ℝ) (fun _ : Config N => ℝ)
noncomputable instance : FiniteDimensional ℝ (EnergySpace N) := by
  classical
  -- `EnergySpace N` is a type synonym of the finite product `∀ σ : Config N, ℝ`.
  infer_instance
def std_basis (σ : Config N) : EnergySpace N :=
  WithLp.toLp 2 (fun τ => if σ = τ then 1 else 0)
noncomputable section
def overlap (σ τ : Config N) : ℝ :=
  (1 / (N : ℝ)) * ∑ i, (spin N σ i) * (spin N τ i)
/-! ### Covariance Kernels -/
def sk_cov_kernel (σ τ : Config N) : ℝ :=
  (N * β^2 / 2) * (overlap N σ τ)^2
def simple_cov_kernel (xi : ℝ → ℝ) (σ τ : Config N) : ℝ :=
  N * β^2 * xi (overlap N σ τ)
/-! ### Thermodynamic Quantities -/
def Z (H : EnergySpace N) : ℝ := ∑ σ, Real.exp (- H σ)
def gibbs_pmf (H : EnergySpace N) (σ : Config N) : ℝ :=
  Real.exp (- H σ) / Z N H
/-! ### Free energy density and its abstract (Fréchet) Hessian -/
end
end SpinGlass
