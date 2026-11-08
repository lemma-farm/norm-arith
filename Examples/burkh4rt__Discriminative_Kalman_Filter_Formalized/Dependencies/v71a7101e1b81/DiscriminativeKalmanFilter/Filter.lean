module
public import Examples.burkh4rt__Discriminative_Kalman_Filter_Formalized.Dependencies.v71a7101e1b81.DiscriminativeKalmanFilter.Densities
set_option autoImplicit false
@[expose] public section
noncomputable section
open MeasureTheory Filter Matrix
open scoped Topology ENNReal
namespace DiscriminativeKalmanFilter
/-- The fixed linear Gaussian state model (2.1): Γ and S are positive definite and S = ASAᵀ + Γ. -/
structure Model (d : ℕ) where
  A : Covariance d
  Γ : Covariance d
  S : Covariance d
  Γ_posDef : Γ.PosDef
  S_posDef : S.PosDef
  stationary : S = A * S * A.transpose + Γ
variable {d : ℕ}
/-- The stationary density p(z) = η_d(z; 0, S). -/
def prior (M : Model d) : Density d := gaussianPDF 0 M.S
/-- The Markov transition density τ(y,z) = η_d(z; Ay, Γ). -/
def transition (M : Model d) (y z : State d) : ℝ :=
  gaussianPDF (M.A *ᵥ y) M.Γ z
/-- The prediction operator (τs)(z) = ∫ τ(y,z)s(y) dy. -/
def predictDensity (M : Model d) (s : Density d) : Density d :=
  fun z => ∫ y, transition M y z * s y ∂volume
/-- The unnormalized weight u τs / p in (B.1). -/
def updateWeight (M : Model d) (s u : Density d) : Density d :=
  fun z => u z * predictDensity M s z / prior M z
/-- Well-definedness in (B.1): measurable weight with finite, strictly positive L¹ norm. -/
def UpdateDefined (M : Model d) (s u : Density d) : Prop :=
  AEStronglyMeasurable (updateWeight M s u) volume ∧
    0 < l1Norm (updateWeight M s u) ∧ l1Norm (updateWeight M s u) < ⊤
/-- The specific normalized update (B.1), also used for the primed inputs in C3. -/
def updateDensity (M : Model d) (s u : Density d) : Density d :=
  fun z => updateWeight M s u z / (l1Norm (updateWeight M s u)).toReal
end DiscriminativeKalmanFilter
