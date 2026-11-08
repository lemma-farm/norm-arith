module
public import Examples.burkh4rt__Discriminative_Kalman_Filter_Formalized.Dependencies.v71a7101e1b81.DiscriminativeKalmanFilter.Proof.DensityTools
set_option autoImplicit false
@[expose] public section
noncomputable section
open MeasureTheory Filter Matrix
open scoped Topology ENNReal
namespace DiscriminativeKalmanFilter.Proof
theorem C1 {d : ℕ} [NeZero d] (M : Model d) (D : Problem M)
    (h : Assumptions M D) : Weakly D.s' D.P :=
  weakly_of_l1Distance D.s_pdf (fun n => (D.s'_gaussian n).1) h.A1 h.A2
theorem C2 {d : ℕ} [NeZero d] (M : Model d) (D : Problem M)
    (h : Assumptions M D) : Weakly D.u' (Measure.dirac D.b) :=
  weakly_of_l1Distance D.u_pdf (fun n => (D.u'_gaussian n).1) h.A3 h.A4
end DiscriminativeKalmanFilter.Proof
