module

public import SubdiffusiveProcess.Sobolev.ResponsePositivity
public import SubdiffusiveProcess.Variational.DualEnergy
public import SubdiffusiveProcess.Sobolev.ResponseSpace
public import Mathlib

@[expose] public section

open Filter MeasureTheory Set TopologicalSpace
open scoped ENNReal NNReal Topology
/-! The weak lower bound for the literal dual energy follows from the actual
finite-coefficient variational formula and convergence of volume responses. -/

namespace SubdiffusiveProcess

theorem quadraticDual_le_liminf_responseForm
    {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
    (S : ResponseSpace Ω) (a : ℕ → PositiveCoefficient Ω)
    (G : DomainL2 Ω →L[ℝ] DomainL2 Ω)
    (uN : ℕ → S.space) (u : DomainL2 Ω)
    (hweak : ∀ f : DomainL2 Ω,
      Tendsto (fun n => inner ℝ f (uN n).val.1) atTop (𝓝 (inner ℝ f u)))
    (hresponse : ∀ f : DomainL2 Ω,
      Tendsto (fun n => inverseResponse S (a n)
        ((sobolevVolumeLoad f).comp S.space.subtypeL)) atTop
        (𝓝 (inner ℝ f (G f)))) :
    (⨆ f : DomainL2 Ω, ((2 * inner ℝ f u - inner ℝ f (G f) : ℝ) : EReal)) ≤
      Filter.liminf (fun n => ((responseForm S (a n) (uN n) (uN n) : ℝ) : EReal)) atTop := by
  refine iSup_le fun f => ?_
  let L : S.space →L[ℝ] ℝ := (sobolevVolumeLoad f).comp S.space.subtypeL
  have hfinite : ∀ n, 2 * inner ℝ f (uN n).val.1 - inverseResponse S (a n) L ≤
      responseForm S (a n) (uN n) (uN n) := by
    intro n
    have hmax := (inverseResponse_isGreatest S (a n) L).2
      (show 2 * L (uN n) - responseForm S (a n) (uN n) (uN n) ∈
        Set.range (fun v : S.space => 2 * L v - responseForm S (a n) v v) from
        ⟨uN n, rfl⟩)
    change 2 * inner ℝ f (uN n).val.1 - responseForm S (a n) (uN n) (uN n) ≤
      inverseResponse S (a n) L at hmax
    linarith
  have hreal : Tendsto
      (fun n => 2 * inner ℝ f (uN n).val.1 - inverseResponse S (a n) L) atTop
      (𝓝 (2 * inner ℝ f u - inner ℝ f (G f))) := by
    exact ((tendsto_const_nhds.mul (hweak f)).sub (hresponse f))
  have hereal : Tendsto
      (fun n => ((2 * inner ℝ f (uN n).val.1 - inverseResponse S (a n) L : ℝ) : EReal))
      atTop (𝓝 ((2 * inner ℝ f u - inner ℝ f (G f) : ℝ) : EReal)) :=
    EReal.tendsto_coe.mpr hreal
  calc
    ((2 * inner ℝ f u - inner ℝ f (G f) : ℝ) : EReal) =
        Filter.liminf
          (fun n => ((2 * inner ℝ f (uN n).val.1 - inverseResponse S (a n) L : ℝ) : EReal))
          atTop := hereal.liminf_eq.symm
    _ ≤ Filter.liminf
        (fun n => ((responseForm S (a n) (uN n) (uN n) : ℝ) : EReal)) atTop :=
      liminf_le_liminf (Eventually.of_forall fun n => EReal.coe_le_coe_iff.mpr (hfinite n))

                                                                                    
                                        
                                              
                                                         
                                     
                                                                  
                                                  
                                
                                                 
                                                                              
                      
                     
                                                                                      
                             
                                                                                 
                                                                                                 
                    
                                                                                       
                                                   
                                  
                          
                                                                                
                                                                                 
                                       
                                     
                                              
                                                               

end SubdiffusiveProcess
