/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FalconerThetaGauge.SpaceSplittingFarSumMeasures
public import Mathlib
/-! # Genuine far cross-term summation retains the root four-point measure -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function Finset
open scoped Classical RealInnerProductSpace

namespace FalconerThetaGauge

open GaugeFrostman GaugeSeparatedMeasures

def spaceSplittingFarCrossSum (ρ : Measure Plane) (a p : ℕ) (X Y : Fin 2 → ℤ)
    (b₁ b₂ : Plane → UnitCircle → ℝ) (K v : ℕ) : ℝ :=
  ∑ P ∈ spaceSplittingFinePairs ρ a p X Y,
    ∑ Q ∈ spaceSplittingFinePairs ρ a p X Y,
      if spaceSplittingNear p P Q then 0 else
        |∫ z, inner ℝ
          (spaceSplittingJointAmplitude ρ ρ (dyadicCube p P.1) (dyadicCube p P.2) b₁ b₂ z)
          (spaceSplittingJointAmplitude ρ ρ (dyadicCube p Q.1) (dyadicCube p Q.2) b₁ b₂ z)
          ∂maskedFourierJointMeasure K v|

theorem spaceSplittingRootFourMeasure_real_univ (ρ : Measure Plane) [IsFiniteMeasure ρ]
    (a : ℕ) (X Y : Fin 2 → ℤ) :
    (spaceSplittingRootFourMeasure ρ a X Y).real univ =
      (ρ.real (dyadicCube a X) * ρ.real (dyadicCube a Y)) ^ 2 := by
  have hm (μ ν : Measure (Plane × Plane)) [SFinite ν] :
      (μ.prod ν).real univ = μ.real univ * ν.real univ := by
    simpa only [univ_prod_univ] using measureReal_prod_prod (μ := μ) (ν := ν) univ univ
  have hm' (μ ν : Measure Plane) [SFinite ν] :
      (μ.prod ν).real univ = μ.real univ * ν.real univ := by
    simpa only [univ_prod_univ] using measureReal_prod_prod (μ := μ) (ν := ν) univ univ
  rw [spaceSplittingRootFourMeasure, hm, hm', hm']
  simp only [Measure.real, Measure.restrict_apply_univ]
  ring

                                                                                              
                                                                 
                                                                            
                                                      
                                                                   
                                                                   
                                  
                                               
                                                                                    
                                                      
                                                                          
                                                        
                                                          
                                                                      
                                         
                                                   
                                                                   
                                                             
                                         
                                            
                                                  
                                     
                                                    
                                              
                     
                                                                                          
                                                                                          
                                            
                                                               
                                          
                         
                                                           
                          
                                                                                 
                                                                                   
                                          
                            
                                                                                              
                                           
                                                                         
                                                                           
                                                                         
                                        
                                    
                                                                                   
      
                                                
                                                
                                                                   
                                                                           
                                                              
                                                                 
               
                                                               
                                                                       

end FalconerThetaGauge
