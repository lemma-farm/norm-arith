-- SPDX-License-Identifier: Apache-2.0
module
public import Examples.pmaronow__slowequilibration_palomar.Dependencies.vf17a84b65665.SlowEquilibration.SphericalPairRegression
set_option autoImplicit false
/-! Actual low-order two-point derivative covariances of the finite tensor
field at arbitrary overlap. These are coefficient-space Gaussian covariances,
with the literal N factors retained. -/
@[expose] public section
namespace SlowEquilibration.SphericalTwoPointCovariance
noncomputable section
open MeasureTheory ProbabilityTheory Set Function
open scoped Topology BigOperators RealInnerProductSpace
open SphericalModel SphericalGaussianJet
open SphericalAging.FiniteModel SphericalAging.HamiltonianDerivativeCovariance
open SphericalAging.HamiltonianTangentHessianCovariance
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 700000
lemma pure_gradient_value_covariance {N p : ℕ} (hN : 0 < N)
    (x y u : SphericalModel.Vector N) :
    cov[fun J : PureDisorder N p => iteratedFDeriv ℝ 1 (Hamiltonian N p J) x (fun _ => u),
      fun J => iteratedFDeriv ℝ 0 (Hamiltonian N p J) y (fun i => Fin.elim0 i);PureLaw N p]=
      (p:ℝ)*overlap x y^(p-1)*inner ℝ u y := by
  rw [covariance_eq_sub (Hamiltonian_derivative_memLp 1 x (fun _ => u))
    (Hamiltonian_derivative_memLp 0 y (fun i => Fin.elim0 i))]
  simp only [Hamiltonian_derivative_mean,zero_mul,sub_zero,Pi.mul_apply]
  rw [Hamiltonian_derivative_covariance_gram]
  simp only [coefficientDerivative,iteratedFDeriv_one_apply,iteratedFDeriv_zero_apply]
  rw [coefficient_gradient_gram_left]
  calc
    _=(p:ℝ)*(normalization N p^2*(inner ℝ x y)^(p-1))*inner ℝ u y := by ring
    _=_ := by rw [normalization_first_power hN];rfl
theorem gradient_value_covariance {N P : ℕ} (hN : 0 < N) (c : Degree P → ℝ)
    (hc : ∀ p,0 ≤ c p) (x y u : SphericalModel.Vector N) :
    cov[jet c 1 x (fun _ => u),jet c 0 y (fun i => Fin.elim0 i);disorderLaw N P]=
      firstCovariance c (overlap x y)*inner ℝ u y := by
  rw [jet_covariance c hc]
  simp_rw [pure_gradient_value_covariance hN]
  unfold firstCovariance
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro p hp
  ring
def thirdCovariance {P : ℕ} (c : Degree P → ℝ) (r : ℝ) : ℝ :=
  ∑ p : Degree P,c p*(p.val.val:ℝ)*((p.val.val:ℝ)-1)*((p.val.val:ℝ)-2)*r^(p.val.val-3)
lemma overlap_comm {N : ℕ} (x y : SphericalModel.Vector N) : overlap y x=overlap x y := by
  unfold overlap
  rw [real_inner_comm]
def valueProfileBound {P : ℕ} (c : Degree P → ℝ) : ℝ := ∑ p : Degree P,|c p|
def firstProfileBound {P : ℕ} (c : Degree P → ℝ) : ℝ := ∑ p : Degree P,|c p*(p.val.val:ℝ)|
def secondProfileBound {P : ℕ} (c : Degree P → ℝ) : ℝ := ∑ p : Degree P,|c p*(p.val.val:ℝ)*((p.val.val:ℝ)-1)|
def thirdProfileBound {P : ℕ} (c : Degree P → ℝ) : ℝ := ∑ p : Degree P,|c p*(p.val.val:ℝ)*((p.val.val:ℝ)-1)*((p.val.val:ℝ)-2)|
end
end SlowEquilibration.SphericalTwoPointCovariance
