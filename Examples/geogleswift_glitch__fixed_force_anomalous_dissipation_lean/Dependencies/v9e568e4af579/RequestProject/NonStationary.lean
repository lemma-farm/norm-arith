module
public import Examples.geogleswift_glitch__fixed_force_anomalous_dissipation_lean.Dependencies.v9e568e4af579.RequestProject.WeightedFourier
public import Examples.geogleswift_glitch__fixed_force_anomalous_dissipation_lean.Dependencies.v9e568e4af579.RequestProject.TorusCalc
/-!
# Non-stationary phase for low outputs (Lemma 3.4)

If `|DΨ(y)ᵀe| ≥ 4a` and `|ξ + n| ≤ aρ` with `ξ = ρe`, the phase `φ(y) = ξ·w(y) - n·y` of
`c_n^Ψ(ξ)` has gradient `V = DΨᵀξ - (ξ + n)` of length `≥ 3aρ`.  With `W = V/|V|²` one has
`W·∇e^{2πiφ} = 2πi e^{2πiφ}`, so `∫ g e^{2πiφ} = ∫ (Tg) e^{2πiφ}` with
`Tg = -(2πi)⁻¹ div(gW)`.  Since all derivatives of `W` up to order `J` are `O(1/ρ)`,
`|c_n| ≤ sup|T^J 1| = O(ρ^{-J})`; there are `O(ρ²)` such `n`.
-/
@[expose] public section
open MeasureTheory Set Filter Topology Real
open scoped ENNReal ContDiff Matrix NNReal
noncomputable section
namespace AnomDiss
/-- Uniform bound `A` on all iterated derivatives of order `≤ M`. -/
def SymBd (M : ℕ) (A : ℝ) (g : Pt 2 → ℂ) : Prop :=
  ∀ k ≤ M, ∀ y, ‖iteratedFDeriv ℝ k g y‖ ≤ A
lemma SymBd.mono {M M' : ℕ} {A A' : ℝ} {g : Pt 2 → ℂ} (h : SymBd M A g) (hM : M' ≤ M)
    (hA : A ≤ A') : SymBd M' A' g :=
  fun k hk y => (h k (hk.trans hM) y).trans hA
end AnomDiss
