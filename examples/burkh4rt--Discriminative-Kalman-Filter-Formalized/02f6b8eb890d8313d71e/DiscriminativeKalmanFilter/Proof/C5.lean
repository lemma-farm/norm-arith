module
public import DiscriminativeKalmanFilter.Proof.UpdateCancellation
public import DiscriminativeKalmanFilter.Proof.C3C4

@[expose] public section

noncomputable section
open MeasureTheory Filter Matrix
open scoped Topology ENNReal
namespace DiscriminativeKalmanFilter.Proof

/-- The five-term argument (B.2), with eventual Gaussian validity supplied separately. -/
theorem C5_of_C3_C4 {d : ℕ} [NeZero d] (M : Model d) (D : Problem M)
    (h : Assumptions M D)
    (h3 : ∀ᶠ n in atTop, UpdateDefined M (D.s' n) (D.u' n) ∧ IsGaussianPDF (D.p' M n))
    (h4 : Weakly (D.p' M) (Measure.dirac D.b)) :
    Tendsto (fun n => l1Distance (D.p M n) (D.p' M n)) atTop (𝓝 0) := by
  classical
  have hp n : IsPDF (D.p M n) :=
    updateDensity_isPDF M (D.s_pdf n) (D.u_pdf n) (D.original_defined n)
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
    weakly_eventuallyEq (heq.mono fun _ hn => hn.symm) h4
  let g := gaussianBCF 0 M.S_posDef
  have hg : ∀ z, 0 ≤ g z := fun z => (gaussianPDF_pos 0 M.S_posDef z).le
  have hgb : 0 < g D.b := gaussianPDF_pos 0 M.S_posDef D.b
  let r : Density d → Density d := fun f z => f z * prior M z /
    (∫ y, f y * prior M y ∂volume)
  have hr {f : Density d} (hf : IsPDF f) : Integrable (r f) volume :=
    (bounded_test_integrable hf.2.1 g).div_const _
  have hleft : Tendsto (fun n => (l1Distance (D.p M n) (r (D.p M n))).toReal)
      atTop (𝓝 0) := weakly_dirac_reweight hp h.A5 g hg hgb
  have hright : Tendsto (fun n => (l1Distance (q n) (r (q n))).toReal)
      atTop (𝓝 0) := weakly_dirac_reweight hq hqw g hg hgb
  have hmiddle := kernelProduct_normalized_tendsto M D.s_pdf
    (fun n => (D.s'_gaussian n).1) D.u_pdf (fun n => (D.u'_gaussian n).1)
    D.P D.b h.A1 (C1 M D h) h.A3 (C2 M D h) h.A2 h.A4
  have hmid : Tendsto (fun n => (l1Distance (r (D.p M n)) (r (q n))).toReal)
      atTop (𝓝 0) := by
    apply hmiddle.congr'
    filter_upwards [h3, heq] with n hn hqn
    have hl := normalized_update_times_prior M (D.original_defined n)
    have hr' := normalized_update_times_prior M hn.1
    change r (D.p M n) = _ at hl
    change r (D.p' M n) = _ at hr'
    rw [hqn, hl, hr']
  have htotal : Tendsto (fun n => (l1Distance (D.p M n) (q n)).toReal) atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => ENNReal.toReal_nonneg)
      (g := fun n => (l1Distance (D.p M n) (r (D.p M n))).toReal +
        (l1Distance (r (D.p M n)) (r (q n))).toReal +
        (l1Distance (q n) (r (q n))).toReal)
    · intro n
      have h1 := l1Distance_triangle (hp n).2.1 (hr (hp n)) (hq n).2.1
      have h2 := l1Distance_triangle (hr (hp n)) (hr (hq n)) (hq n).2.1
      rw [l1Distance_comm (r (q n)) (q n)] at h2
      linarith
    · simpa using (hleft.add hmid).add hright
  have hENN := (l1Distance_zero_tendsto_iff (fun n => (hp n).2.1)
    (fun n => (hq n).2.1)).mpr htotal
  apply hENN.congr'
  filter_upwards [heq] with n hn
  rw [hn]

                                                                   
                                                                     
                           
                                                                        
                                         
                               

end DiscriminativeKalmanFilter.Proof
