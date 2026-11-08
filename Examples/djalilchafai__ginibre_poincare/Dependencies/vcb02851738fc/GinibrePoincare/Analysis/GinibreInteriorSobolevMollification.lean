module
public import Examples.djalilchafai__ginibre_poincare.Dependencies.vcb02851738fc.GinibrePoincare.Analysis.GinibreInteriorWeakGradient
public import Examples.djalilchafai__ginibre_poincare.Dependencies.vcb02851738fc.GinibrePoincare.Analysis.LebesgueL2MollificationMaps
@[expose] public section
/-! # Simultaneous interior weak-Sobolev mollification

For actual Ginibre weak pairs with compact representatives supported away from
collisions, the classical gradient of the concrete smooth convolution represents
the vector L² bump average. Both values and gradients converge in Lebesgue L².
-/
open MeasureTheory Filter ContinuousLinearMap
open scoped Topology ContDiff Convolution
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 400000
variable (n : ℕ) (hn : 0 < n)
    (u : Lp ℝ 2 (ginibreMeasure n))
    (g : Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n))
    (hg : IsGinibreDistributionalGradient n u g)
    (f : Configuration n → ℝ)
    (h : Configuration n → EuclideanSpace ℝ (Fin n × Fin 2))
    (hf : (u : Configuration n → ℝ) =ᵐ[ginibreMeasure n] f)
    (hh : (g : Configuration n → EuclideanSpace ℝ (Fin n × Fin 2)) =ᵐ[ginibreMeasure n] h)
    (hfc : HasCompactSupport f) (hhc : HasCompactSupport h)
    (hfs : tsupport f ⊆ {z | CollisionFree z}) (hhs : tsupport h ⊆ {z | CollisionFree z})
include hn u g hg hf hh hfc hhc hfs hhs
end
end GinibrePoincare
