module
public import Examples.nitromannitol__subdiffusive_process.Dependencies.v1845306bb08d.SubdiffusiveProcess.Sobolev.AffineData
public import Examples.nitromannitol__subdiffusive_process.Dependencies.v1845306bb08d.SubdiffusiveProcess.Sobolev.DirichletResponse
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
set_option warn.classDefReducibility false
@[expose] public section
/-!
# Actual affine finite-volume responses

These are the unnormalized primal and inverse-Neumann scalar responses used
in Section 3.2 and the original-grid reflection argument. Their competitors
are the concrete killed and mean-zero Sobolev spaces. Only ordinary Poincare
and finite-cutoff ellipticity enter their construction. Matrix normalization
and finite-partition subadditivity are separate obligations.
-/
open MeasureTheory Filter Set TopologicalSpace
open scoped ENNReal NNReal
noncomputable section
namespace SubdiffusiveProcess
variable {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
/-- The full Sobolev form has the same unnormalized coordinate integral. -/
theorem sobolevCoefficientForm_apply (a : PositiveCoefficient Ω) (u v : SobolevData Ω) :
    sobolevCoefficientForm a u v = ∑ i : Fin d,
      ∫ x in (Ω : Set (SpatialCoordinates d)), a.val x * (u.2 i x * v.2 i x) :=
  weightedGradientForm_apply a.val _ _
variable [IsFiniteMeasure (volume.restrict (Ω : Set (SpatialCoordinates d)))]
/-- The energy of an affine competitor is its squared slope times coefficient mass. -/
theorem affineSobolevData_energy (hΩ : Bornology.IsBounded (Ω : Set (SpatialCoordinates d)))
    (a : PositiveCoefficient Ω) (p : Fin d → ℝ) (c : ℝ) :
    sobolevCoefficientForm a (affineSobolevData hΩ p c) (affineSobolevData hΩ p c) =
      (∑ i : Fin d, (p i) ^ 2) * ∫ x in (Ω : Set (SpatialCoordinates d)), a.val x := by
  rw [sobolevCoefficientForm_apply, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  calc
    _ = ∫ x in (Ω : Set (SpatialCoordinates d)), a.val x * (p i) ^ 2 := by
      apply integral_congr_ae
      filter_upwards [domainConstantL2_coeFn (Ω := Ω) (p i)] with x hx
      change a.val x * ((domainConstantL2 (Ω := Ω) (p i)) x *
        (domainConstantL2 (Ω := Ω) (p i)) x) = _
      rw [hx, pow_two]
    _ = _ := by rw [integral_mul_const, mul_comm]
/-- The affine Dirichlet minimum, with the prescribed slope and killed variations. -/
def affineDirichletResponse (hΩ : Bornology.IsBounded (Ω : Set (SpatialCoordinates d)))
    (hP : ∃ K : ℝ≥0, ∀ z : killedSobolevGraph Ω,
      ‖(z : SobolevData Ω).1‖ ≤ K * ‖subspaceGradient (killedSobolevGraph Ω) z‖)
    (a : PositiveCoefficient Ω) (p : Fin d → ℝ) : ℝ :=
  dirichletResponse (killedResponseSpace hP) a (affineSobolev hΩ p 0)
theorem affineDirichletResponse_le_affine_energy
    (hΩ : Bornology.IsBounded (Ω : Set (SpatialCoordinates d)))
    (hP : ∃ K : ℝ≥0, ∀ z : killedSobolevGraph Ω,
      ‖(z : SobolevData Ω).1‖ ≤ K * ‖subspaceGradient (killedSobolevGraph Ω) z‖)
    (a : PositiveCoefficient Ω) (p : Fin d → ℝ) :
    affineDirichletResponse hΩ hP a p ≤
      (∑ i : Fin d, (p i) ^ 2) * ∫ x in (Ω : Set (SpatialCoordinates d)), a.val x := by
  have h := (dirichletResponse_isLeast (killedResponseSpace hP) a
    (affineSobolev hΩ p 0)).2 (Set.mem_range_self (0 : killedSobolevGraph Ω))
  simpa only [affineDirichletResponse, ZeroMemClass.coe_zero, add_zero, affineSobolev,
    affineSobolevData_energy] using h
/-- The inverse affine Neumann response, on the actual mean-zero Sobolev space. -/
def affineInverseNeumannResponse
    (hP : ∃ K : ℝ≥0, ∀ z : meanZeroSobolevGraph Ω,
      ‖(z : SobolevData Ω).1‖ ≤ K * ‖subspaceGradient (meanZeroSobolevGraph Ω) z‖)
    (a : PositiveCoefficient Ω) (p : Fin d → ℝ) : ℝ :=
  inverseResponse (meanZeroResponseSpace hP) a
    ((affineNeumannLoad p).comp (subspaceGradient (meanZeroSobolevGraph Ω)))
end SubdiffusiveProcess
