module
public import Examples.burkh4rt__Discriminative_Kalman_Filter_Formalized.Dependencies.v71a7101e1b81.DiscriminativeKalmanFilter.Filter
set_option autoImplicit false
@[expose] public section
noncomputable section
open MeasureTheory Filter Matrix
open scoped Topology ENNReal
namespace DiscriminativeKalmanFilter
variable {d : ℕ}
/-- The four fixed sequences, their density requirements, b, P, and validity of every exact update.
The Gaussian approximants are arbitrary witnesses for A2 and A4, not selected by a choice rule. -/
structure Problem (M : Model d) where
  s : ℕ+ → Density d
  u : ℕ+ → Density d
  s' : ℕ+ → Density d
  u' : ℕ+ → Density d
  b : State d
  P : ProbabilityMeasure (State d)
  s_pdf : ∀ n, IsPDF (s n)
  u_pdf : ∀ n, IsPDF (u n)
  s'_gaussian : ∀ n, IsGaussianPDF (s' n)
  u'_gaussian : ∀ n, IsGaussianPDF (u' n)
  original_defined : ∀ n, UpdateDefined M (s n) (u n)
/-- The exact pdf pₙ in (B.1). -/
def Problem.p (M : Model d) (D : Problem M) (n : ℕ+) : Density d :=
  updateDensity M (D.s n) (D.u n)
/-- The prescribed Gaussian approximation p′ₙ in C3; validity is a conclusion. -/
def Problem.p' (M : Model d) (D : Problem M) (n : ℕ+) : Density d :=
  updateDensity M (D.s' n) (D.u' n)
/-- Exactly the five limits A1–A5 of Theorem 2. Gaussianity of the witnesses is in Problem. -/
structure Assumptions (M : Model d) (D : Problem M) : Prop where
  A1 : Weakly D.s D.P
  A2 : Tendsto (fun n => l1Distance (D.s n) (D.s' n)) atTop (𝓝 0)
  A3 : Weakly D.u (Measure.dirac D.b)
  A4 : Tendsto (fun n => l1Distance (D.u n) (D.u' n)) atTop (𝓝 0)
  A5 : Weakly (D.p M) (Measure.dirac D.b)
end DiscriminativeKalmanFilter
