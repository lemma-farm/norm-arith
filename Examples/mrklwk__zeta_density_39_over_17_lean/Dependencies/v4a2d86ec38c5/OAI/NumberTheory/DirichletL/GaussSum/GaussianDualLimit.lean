module
public import Examples.mrklwk__zeta_density_39_over_17_lean.Dependencies.v4a2d86ec38c5.OAI.NumberTheory.DirichletL.Poisson.BinaryGaussian
public import Mathlib
set_option autoImplicit false
@[expose] public section
namespace OAI
noncomputable section
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
namespace ActualEisensteinCubic
end ActualEisensteinCubic
namespace OscillatoryDeterminant
open Complex
def q (a b : ℂ) : ℂ := a*a-a*b+b*b
noncomputable def A (t a b : ℂ) : ℂ := t + 2*Complex.I*b/q a b
noncomputable def B (t a b : ℂ) : ℂ := -t/2-2*Complex.I*a/q a b
noncomputable def D (t a b : ℂ) : ℂ := t + 2*Complex.I*(a-b)/q a b
end OscillatoryDeterminant
namespace ActualEisensteinCubic
open EisensteinEmbedding ConcreteTraceCRT Complex
end ActualEisensteinCubic
namespace EisensteinFiberShift
def Q (x y : ℝ) : ℝ := x*x-x*y+y*y
def q (a b : ℝ) : ℝ := Q a b
end EisensteinFiberShift
namespace ShortDraftLatticeCount
open ActualEisensteinCoordinates
noncomputable def rowNormBall (H : ℕ) : Finset O := by
  classical
  let I : Finset ℤ := Finset.Icc (-((H : ℤ) + 1)) ((H : ℤ) + 1)
  exact (I.product I).image (fun v => eval v.1 v.2)
end ShortDraftLatticeCount
namespace EisensteinGaussianPrefactor
end EisensteinGaussianPrefactor
namespace ActualEisensteinCubic
open EisensteinEmbedding ConcreteTraceCRT Complex
end ActualEisensteinCubic
namespace EisensteinGaussianPrefactor
end EisensteinGaussianPrefactor
namespace ActualEisensteinCubic
end ActualEisensteinCubic
namespace OscillatoryDeterminant
open Complex
noncomputable def r (t a b : ℂ) : ℂ := 1 + 3 * q a b * t^2 / 16
end OscillatoryDeterminant
open Filter Real Asymptotics
namespace RankTwoLimit
section
open scoped Topology
open RankTwoPoisson RankTwoEisShift Filter
end
open scoped Topology
open Filter
end RankTwoLimit
end
end OAI
