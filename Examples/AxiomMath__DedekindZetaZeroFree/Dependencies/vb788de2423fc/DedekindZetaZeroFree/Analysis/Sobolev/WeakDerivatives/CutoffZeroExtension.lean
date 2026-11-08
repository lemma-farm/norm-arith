module
public import Examples.AxiomMath__DedekindZetaZeroFree.Dependencies.vb788de2423fc.DedekindZetaZeroFree.Analysis.Sobolev.WeakDerivatives.MultiIndexLeibnizRule
set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace DedekindZetaZeroFree.KPLocalCubeSobolevJets.Interior
open MeasureTheory KPContLocalNorm TopologicalSpace
structure GlobalWeakSobolev (n k : ℕ) where
  derivatives : MultiIndex n k → Lp ℂ 2 (volume : Measure (Space n))
  weak_derivatives : ∀ (α : MultiIndex n k)
    (φ : TestFunction (⊤ : Opens (Space n)) ℂ ⊤),
    (∫ x, derivatives (⟨fun _ => 0, by simp⟩ : MultiIndex n k) x *
      coordinateDerivative α (fun y => φ y) x) =
      (-1 : ℂ) ^ α.degree * (∫ x, derivatives α x * φ x)
open WeakJets.Raw Filter
open scoped Topology
end DedekindZetaZeroFree.KPLocalCubeSobolevJets.Interior
end
