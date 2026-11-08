module
public import DiscriminativeKalmanFilter.Proof.DensityTools

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
