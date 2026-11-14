module

public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Data.PNat.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.MeasureTheory.Measure.FiniteMeasureProd
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric

-- ==== Examples.burkh4rt__Discriminative_Kalman_Filter_Formalized.Dependencies.v71a7101e1b81.DiscriminativeKalmanFilter.Densities ====
public section
set_option autoImplicit false
@[expose] public section
noncomputable section
open MeasureTheory Filter Matrix
open scoped Topology ENNReal
namespace DiscriminativeKalmanFilter
/-- The state space ℝᵈ with its standard Borel structure and Lebesgue measure. -/
abbrev State (d : ℕ) := Fin d → ℝ
/-- Real d × d matrices; positive definiteness is required explicitly. -/
abbrev Covariance (d : ℕ) := Matrix (Fin d) (Fin d) ℝ
/-- Real-valued functions on the state space. -/
abbrev Density (d : ℕ) := State d → ℝ
variable {d : ℕ}
/-- η_d(z; m, C), the normalized multivariate Gaussian formula. Used with C positive definite. -/
def gaussianPDF (m : State d) (C : Covariance d) (z : State d) : ℝ :=
  (Real.sqrt ((2 * Real.pi) ^ d * C.det))⁻¹ *
    Real.exp (-((z - m) ⬝ᵥ (C⁻¹ *ᵥ (z - m))) / 2)
/-- A Lebesgue probability density: nonnegative almost everywhere, integrable, and of integral one. -/
def IsPDF (f : Density d) : Prop :=
  (∀ᵐ z ∂volume, 0 ≤ f z) ∧ Integrable f volume ∧ (∫ z, f z ∂volume) = 1
/-- A pdf equal almost everywhere to a nondegenerate Gaussian density. -/
def IsGaussianPDF (f : Density d) : Prop :=
  IsPDF f ∧ ∃ (m : State d) (C : Covariance d), C.PosDef ∧
    f =ᵐ[volume] gaussianPDF m C
/-- The measure with density f relative to Lebesgue measure. -/
def densityMeasure (f : Density d) : Measure (State d) :=
  volume.withDensity (fun z => ENNReal.ofReal (f z))
/-- Lebesgue L¹ norm, extended-valued so invalid weights are not mistaken for integrable ones. -/
def l1Norm (f : Density d) : ℝ≥0∞ :=
  ∫⁻ z, ENNReal.ofReal |f z| ∂volume
/-- L¹ distance between two densities. Finite when both are pdfs. -/
def l1Distance (f g : Density d) : ℝ≥0∞ := l1Norm (f - g)
/-- Weak convergence tested against every bounded continuous real function, as in Appendix B. -/
def Weakly (f : ℕ+ → Density d) (P : Measure (State d)) : Prop :=
  ∀ g : BoundedContinuousFunction (State d) ℝ,
    Tendsto (fun n => ∫ z, g z ∂densityMeasure (f n)) atTop (𝓝 (∫ z, g z ∂P))
end DiscriminativeKalmanFilter

end
end
end

-- ==== Examples.burkh4rt__Discriminative_Kalman_Filter_Formalized.Dependencies.v71a7101e1b81.DiscriminativeKalmanFilter.Filter ====
public section
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

end
end
end

-- ==== Examples.burkh4rt__Discriminative_Kalman_Filter_Formalized.Dependencies.v71a7101e1b81.DiscriminativeKalmanFilter.Assumptions ====
public section
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

end
end
end

-- ==== Examples.burkh4rt__Discriminative_Kalman_Filter_Formalized.Dependencies.v71a7101e1b81.DiscriminativeKalmanFilter.Proof.GaussianBasics ====
public section
set_option autoImplicit false
@[expose] public section
noncomputable section
open MeasureTheory Filter Matrix
open scoped Topology ENNReal
namespace DiscriminativeKalmanFilter.Proof
variable {d : ℕ}
set_option linter.unusedVariables false in
axiom _root_.DiscriminativeKalmanFilter.Proof.gaussianPDF_pos : ∀ {d : ℕ} (m : DiscriminativeKalmanFilter.State d) {C : DiscriminativeKalmanFilter.Covariance d},
  Matrix.PosDef C →
    ∀ (z : DiscriminativeKalmanFilter.State d), 0 < DiscriminativeKalmanFilter.gaussianPDF m C z
set_option linter.unusedVariables false in
axiom _root_.DiscriminativeKalmanFilter.Proof.gaussianPDF_continuous : ∀ {d : ℕ} (m : DiscriminativeKalmanFilter.State d) (C : DiscriminativeKalmanFilter.Covariance d),
  Continuous (DiscriminativeKalmanFilter.gaussianPDF m C)
set_option linter.unusedVariables false in
axiom _root_.DiscriminativeKalmanFilter.Proof.gaussianPDF_le : ∀ {d : ℕ} (m : DiscriminativeKalmanFilter.State d) {C : DiscriminativeKalmanFilter.Covariance d},
  Matrix.PosDef C →
    ∀ (z : DiscriminativeKalmanFilter.State d),
      DiscriminativeKalmanFilter.gaussianPDF m C z ≤ DiscriminativeKalmanFilter.gaussianPDF 0 C 0
def gaussianBCF (m : State d) {C : Covariance d} (hC : C.PosDef) :
    BoundedContinuousFunction (State d) ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (gaussianPDF m C)
    (gaussianPDF_continuous m C) (gaussianPDF 0 C 0) (fun z => by
      rw [Real.norm_eq_abs, abs_of_pos (gaussianPDF_pos m hC z)]
      exact gaussianPDF_le m hC z)

end DiscriminativeKalmanFilter.Proof

end
end
end

-- ==== Examples.burkh4rt__Discriminative_Kalman_Filter_Formalized.Examples.Example_02f6b8eb890d8313d71e_C5 ====
set_option autoImplicit false
@[expose] public section
noncomputable section
open MeasureTheory Filter Matrix
open scoped Topology ENNReal
namespace DiscriminativeKalmanFilter.Proof
set_option linter.unusedVariables false in
/-- The five-term argument (B.2), with eventual Gaussian validity supplied separately. -/
theorem C5_of_C3_C4 {d : ℕ} [NeZero d] (M : Model d) (D : Problem M)
    (h : Assumptions M D)
    (h3 : ∀ᶠ n in atTop, UpdateDefined M (D.s' n) (D.u' n) ∧ IsGaussianPDF (D.p' M n))
    (h4 : Weakly (D.p' M) (Measure.dirac D.b)) 
    (h_DiscriminativeKalmanFilter_Proof_weakly_dirac_reweight : ∀ {d : ℕ} {f : ℕ+ → DiscriminativeKalmanFilter.Density d} {b : DiscriminativeKalmanFilter.State d},
      (∀ (n : ℕ+), DiscriminativeKalmanFilter.IsPDF (f n)) →
        DiscriminativeKalmanFilter.Weakly f (MeasureTheory.Measure.dirac b) →
          ∀ (g : BoundedContinuousFunction (DiscriminativeKalmanFilter.State d) ℝ),
            (∀ (z : DiscriminativeKalmanFilter.State d),
                0 ≤ (g : DiscriminativeKalmanFilter.State d → ℝ) z) →
              0 < (g : DiscriminativeKalmanFilter.State d → ℝ) b →
                Filter.Tendsto
                  (fun (n : ℕ+) ↦
                    (DiscriminativeKalmanFilter.l1Distance (f n)
                        fun (z : DiscriminativeKalmanFilter.State d) ↦
                        f n z * (g : DiscriminativeKalmanFilter.State d → ℝ) z /
                          ∫ (y : DiscriminativeKalmanFilter.State d),
                            f n y * (g : DiscriminativeKalmanFilter.State d → ℝ) y).toReal)
                  Filter.atTop (nhds 0))
    (h_DiscriminativeKalmanFilter_Proof_l1Distance_triangle : ∀ {d : ℕ} {f g h : DiscriminativeKalmanFilter.Density d},
      MeasureTheory.Integrable f MeasureTheory.MeasureSpace.volume →
        MeasureTheory.Integrable g MeasureTheory.MeasureSpace.volume →
          MeasureTheory.Integrable h MeasureTheory.MeasureSpace.volume →
            (DiscriminativeKalmanFilter.l1Distance f h).toReal ≤
              (DiscriminativeKalmanFilter.l1Distance f g).toReal +
                (DiscriminativeKalmanFilter.l1Distance g h).toReal)
    (h_DiscriminativeKalmanFilter_Proof_updateDensity_isPDF : ∀ {d : ℕ} (M : DiscriminativeKalmanFilter.Model d) {s u : DiscriminativeKalmanFilter.Density d},
      DiscriminativeKalmanFilter.IsPDF s →
        DiscriminativeKalmanFilter.IsPDF u →
          DiscriminativeKalmanFilter.UpdateDefined M s u →
            DiscriminativeKalmanFilter.IsPDF (DiscriminativeKalmanFilter.updateDensity M s u))
    (h_DiscriminativeKalmanFilter_Proof_weakly_eventuallyEq : ∀ {d : ℕ} {f g : ℕ+ → DiscriminativeKalmanFilter.Density d}
      {P : MeasureTheory.Measure (DiscriminativeKalmanFilter.State d)},
      (∀ᶠ (n : ℕ+) in Filter.atTop, f n = g n) →
        DiscriminativeKalmanFilter.Weakly f P → DiscriminativeKalmanFilter.Weakly g P)
    (h_DiscriminativeKalmanFilter_Proof_kernelProduct_normalized_tendsto : ∀ {d : ℕ} (M : DiscriminativeKalmanFilter.Model d)
      {s s' u u' : ℕ+ → DiscriminativeKalmanFilter.Density d},
      (∀ (n : ℕ+), DiscriminativeKalmanFilter.IsPDF (s n)) →
        (∀ (n : ℕ+), DiscriminativeKalmanFilter.IsPDF (s' n)) →
          (∀ (n : ℕ+), DiscriminativeKalmanFilter.IsPDF (u n)) →
            (∀ (n : ℕ+), DiscriminativeKalmanFilter.IsPDF (u' n)) →
              ∀ (P : MeasureTheory.ProbabilityMeasure (DiscriminativeKalmanFilter.State d))
                (b : DiscriminativeKalmanFilter.State d),
                DiscriminativeKalmanFilter.Weakly s
                    (↑P : MeasureTheory.Measure (DiscriminativeKalmanFilter.State d)) →
                  DiscriminativeKalmanFilter.Weakly s'
                      (↑P : MeasureTheory.Measure (DiscriminativeKalmanFilter.State d)) →
                    DiscriminativeKalmanFilter.Weakly u (MeasureTheory.Measure.dirac b) →
                      DiscriminativeKalmanFilter.Weakly u' (MeasureTheory.Measure.dirac b) →
                        Filter.Tendsto
                            (fun (n : ℕ+) ↦ DiscriminativeKalmanFilter.l1Distance (s n) (s' n))
                            Filter.atTop (nhds 0) →
                          Filter.Tendsto
                              (fun (n : ℕ+) ↦ DiscriminativeKalmanFilter.l1Distance (u n) (u' n))
                              Filter.atTop (nhds 0) →
                            Filter.Tendsto
                              (fun (n : ℕ+) ↦
                                (DiscriminativeKalmanFilter.l1Distance
                                    (fun (z : DiscriminativeKalmanFilter.State d) ↦
                                      u n z * DiscriminativeKalmanFilter.predictDensity M (s n) z /
                                        ∫ (y : DiscriminativeKalmanFilter.State d),
                                          u n y * DiscriminativeKalmanFilter.predictDensity M (s n) y)
                                    fun (z : DiscriminativeKalmanFilter.State d) ↦
                                    u' n z * DiscriminativeKalmanFilter.predictDensity M (s' n) z /
                                      ∫ (y : DiscriminativeKalmanFilter.State d),
                                        u' n y *
                                          DiscriminativeKalmanFilter.predictDensity M (s' n) y).toReal)
                              Filter.atTop (nhds 0))
    (h_DiscriminativeKalmanFilter_Proof_C1 : ∀ {d : ℕ} [NeZero d] (M : DiscriminativeKalmanFilter.Model d)
      (D : DiscriminativeKalmanFilter.Problem M),
      DiscriminativeKalmanFilter.Assumptions M D →
        DiscriminativeKalmanFilter.Weakly D.s'
          (↑D.P : MeasureTheory.Measure (DiscriminativeKalmanFilter.State d)))
    (h_DiscriminativeKalmanFilter_Proof_normalized_update_times_prior : ∀ {d : ℕ} (M : DiscriminativeKalmanFilter.Model d) {s u : DiscriminativeKalmanFilter.Density d},
      DiscriminativeKalmanFilter.UpdateDefined M s u →
        (fun (z : DiscriminativeKalmanFilter.State d) ↦
            DiscriminativeKalmanFilter.updateDensity M s u z * DiscriminativeKalmanFilter.prior M z /
              ∫ (y : DiscriminativeKalmanFilter.State d),
                DiscriminativeKalmanFilter.updateDensity M s u y *
                  DiscriminativeKalmanFilter.prior M y) =
          fun (z : DiscriminativeKalmanFilter.State d) ↦
          u z * DiscriminativeKalmanFilter.predictDensity M s z /
            ∫ (y : DiscriminativeKalmanFilter.State d),
              u y * DiscriminativeKalmanFilter.predictDensity M s y)
    (h_DiscriminativeKalmanFilter_Proof_l1Distance_comm : ∀ {d : ℕ} (f g : DiscriminativeKalmanFilter.Density d),
      DiscriminativeKalmanFilter.l1Distance f g = DiscriminativeKalmanFilter.l1Distance g f)
    (h_DiscriminativeKalmanFilter_Proof_l1Distance_zero_tendsto_iff : ∀ {d : ℕ} {f g : ℕ+ → DiscriminativeKalmanFilter.Density d},
      (∀ (n : ℕ+), MeasureTheory.Integrable (f n) MeasureTheory.MeasureSpace.volume) →
        (∀ (n : ℕ+), MeasureTheory.Integrable (g n) MeasureTheory.MeasureSpace.volume) →
          (Filter.Tendsto (fun (n : ℕ+) ↦ DiscriminativeKalmanFilter.l1Distance (f n) (g n))
              Filter.atTop (nhds 0) ↔
            Filter.Tendsto (fun (n : ℕ+) ↦ (DiscriminativeKalmanFilter.l1Distance (f n) (g n)).toReal)
              Filter.atTop (nhds 0)))
    (h_DiscriminativeKalmanFilter_Proof_C2 : ∀ {d : ℕ} [NeZero d] (M : DiscriminativeKalmanFilter.Model d)
      (D : DiscriminativeKalmanFilter.Problem M),
      DiscriminativeKalmanFilter.Assumptions M D →
        DiscriminativeKalmanFilter.Weakly D.u' (MeasureTheory.Measure.dirac D.b))
    (h_DiscriminativeKalmanFilter_Proof_bounded_test_integrable : ∀ {d : ℕ} {f : DiscriminativeKalmanFilter.Density d},
      MeasureTheory.Integrable f MeasureTheory.MeasureSpace.volume →
        ∀ (g : BoundedContinuousFunction (DiscriminativeKalmanFilter.State d) ℝ),
          MeasureTheory.Integrable
            (fun (z : DiscriminativeKalmanFilter.State d) ↦
              f z * (g : DiscriminativeKalmanFilter.State d → ℝ) z)
            MeasureTheory.MeasureSpace.volume)
    :
    Tendsto (fun n => l1Distance (D.p M n) (D.p' M n)) atTop (𝓝 0) := by
  classical
  have hp n : IsPDF (D.p M n) :=
    h_DiscriminativeKalmanFilter_Proof_updateDensity_isPDF M (D.s_pdf n) (D.u_pdf n) (D.original_defined n)
  let q : ℕ+ → Density d := fun n => if IsPDF (D.p' M n) then D.p' M n else D.p M n
  have hq n : IsPDF (q n) := by
    dsimp [q]
    split
    · assumption
    · exact hp n
  have heq : ∀ᶠ n in atTop, q n = D.p' M n := by
    filter_upwards [h3] with n hn
    exact ite_eq_left hn.2.1
  have hqw : Weakly q (Measure.dirac D.b) :=
    h_DiscriminativeKalmanFilter_Proof_weakly_eventuallyEq (heq.mono fun _ hn => hn.symm) h4
  let g := gaussianBCF 0 M.S_posDef
  have hg : ∀ z, 0 ≤ g z := fun z => (gaussianPDF_pos 0 M.S_posDef z).le
  have hgb : 0 < g D.b := gaussianPDF_pos 0 M.S_posDef D.b
  let r : Density d → Density d := fun f z => f z * prior M z /
    (∫ y, f y * prior M y ∂volume)
  have hr {f : Density d} (hf : IsPDF f) : Integrable (r f) volume :=
    (h_DiscriminativeKalmanFilter_Proof_bounded_test_integrable hf.2.1 g).div_const _
  have hleft : Tendsto (fun n => (l1Distance (D.p M n) (r (D.p M n))).toReal)
      atTop (𝓝 0) := h_DiscriminativeKalmanFilter_Proof_weakly_dirac_reweight hp h.A5 g hg hgb
  have hright : Tendsto (fun n => (l1Distance (q n) (r (q n))).toReal)
      atTop (𝓝 0) := h_DiscriminativeKalmanFilter_Proof_weakly_dirac_reweight hq hqw g hg hgb
  have hmiddle := h_DiscriminativeKalmanFilter_Proof_kernelProduct_normalized_tendsto M D.s_pdf
    (fun n => (D.s'_gaussian n).1) D.u_pdf (fun n => (D.u'_gaussian n).1)
    D.P D.b h.A1 (h_DiscriminativeKalmanFilter_Proof_C1 M D h) h.A3 (h_DiscriminativeKalmanFilter_Proof_C2 M D h) h.A2 h.A4
  have hmid : Tendsto (fun n => (l1Distance (r (D.p M n)) (r (q n))).toReal)
      atTop (𝓝 0) := by
    apply hmiddle.congr'
    filter_upwards [h3, heq] with n hn hqn
    have hl := h_DiscriminativeKalmanFilter_Proof_normalized_update_times_prior M (D.original_defined n)
    have hr' := h_DiscriminativeKalmanFilter_Proof_normalized_update_times_prior M hn.1
    change r (D.p M n) = _ at hl
    change r (D.p' M n) = _ at hr'
    rw [hqn, hl, hr']
  have htotal : Tendsto (fun n => (l1Distance (D.p M n) (q n)).toReal) atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => ENNReal.toReal_nonneg)
      (g := fun n => (l1Distance (D.p M n) (r (D.p M n))).toReal +
        (l1Distance (r (D.p M n)) (r (q n))).toReal +
        (l1Distance (q n) (r (q n))).toReal)
    · intro n
      have h1 := h_DiscriminativeKalmanFilter_Proof_l1Distance_triangle (hp n).2.1 (hr (hp n)) (hq n).2.1
      have h2 := h_DiscriminativeKalmanFilter_Proof_l1Distance_triangle (hr (hp n)) (hr (hq n)) (hq n).2.1
      rw [h_DiscriminativeKalmanFilter_Proof_l1Distance_comm (r (q n)) (q n)] at h2
      linarith
    · simpa using (hleft.add hmid).add hright
  have hENN := (h_DiscriminativeKalmanFilter_Proof_l1Distance_zero_tendsto_iff (fun n => (hp n).2.1)
    (fun n => (hq n).2.1)).mpr htotal
  apply hENN.congr'
  filter_upwards [heq] with n hn
  rw [hn]
end DiscriminativeKalmanFilter.Proof
