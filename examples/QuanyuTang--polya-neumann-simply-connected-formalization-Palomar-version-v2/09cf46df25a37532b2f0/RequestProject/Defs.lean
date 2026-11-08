module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.Topology.Connected.Basic
public import Mathlib.Topology.MetricSpace.Lipschitz
public import Mathlib.Topology.Algebra.Support
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Analysis.Calculus.BumpFunction.Convolution
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.Analysis.Normed.Lp.SmoothApprox
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
public import Mathlib.Analysis.Normed.Module.WeakDual
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.MeasureTheory.Measure.SeparableMeasure
public import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
public import Mathlib.Analysis.Normed.Operator.Compact
public import Mathlib.Tactic

/-!
# Definitions (Section 1 of the paper)

We identify `ℝ²` with `ℂ`, as in the paper.

* `PolyaNeumann.IsDomain`, `PolyaNeumann.IsLipschitzDomain` : (Lipschitz) domains.
* `PolyaNeumann.TestFunction` : `C_c^∞(Ω)` test functions.
* `PolyaNeumann.IsWeakGradient` : weak first derivatives in `L²(Ω)`; an element of
  `L²(Ω)` with a weak gradient is exactly an element of `H¹(Ω)`.
* `PolyaNeumann.neumannEnergy` : the Neumann form `q_Ω[u,u] = ∫_Ω |∇u|²` (equal to `⊤`
  outside `H¹(Ω)`).
* `PolyaNeumann.neumannEigenvalue` : the Neumann eigenvalues `μ_j(Ω)`, defined via the
  min–max (Courant–Fischer) formula of Lemma 3.3 of the paper.
* `PolyaNeumann.neumannCount` : the strict counting function `N_N(E)`.
-/

@[expose] public section

open MeasureTheory

noncomputable section

namespace PolyaNeumann

                                                              
                                                           

                                                                                   
                                                                                          
                                              
                                           
              
                                                                 
                                                           
                                    
                                                              
                                                     

                                                                                         
abbrev L2 (Ω : Set ℂ) := Lp ℂ 2 (volume.restrict Ω)

                                                                  
                                           

                                                                     
def TestFunction (Ω : Set ℂ) (φ : ℂ → ℂ) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ Ω

                                                                                 
                                      
                                                                      
                                              
                                                                       

                                                         
                                                                  

                                                                              
                                                     
                                                                              

                                               
                                                
                                          

                                                                                      
               
                                                                  
                                                                                   
                                                      
                                                              
                                                      

                                                                      
                                                  
                                            

end PolyaNeumann

end
