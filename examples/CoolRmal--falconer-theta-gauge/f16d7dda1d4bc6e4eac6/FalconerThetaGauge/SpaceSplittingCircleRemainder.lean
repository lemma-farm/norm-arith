module

public import FalconerThetaGauge.SpaceSplittingBudgetRemainder
public import FalconerThetaGauge.SpaceSplittingCircle
public import Mathlib
/-! # The actual far circular integral has a uniformly small stationary remainder -/

@[expose] public section

noncomputable section

open MeasureTheory

namespace FalconerThetaGauge

/-- Both genuine stationary contributions to the actual built-symbol circular integral. -/
def spaceSplittingStationaryMain (T : ℕ) (b : Plane → UnitCircle → ℝ)
    (r : ℝ) (x x' : Plane) : ℂ :=
  (Real.sqrt (2 * Real.pi / (r * dist x x')) : ℂ) *
    (Complex.exp (-((r * dist x x' - Real.pi / 4 : ℝ) : ℂ) * Complex.I) *
      ∑ j ∈ Finset.range T, ((r * dist x x' : ℝ) : ℂ)⁻¹ ^ j *
        stationaryPhaseOperator j (builtSymbolPairAngularAmplitude b b x x')
          (radialAngle 0 (x - x')) +
    Complex.exp (((r * dist x x' - Real.pi / 4 : ℝ) : ℂ) * Complex.I) *
      ∑ j ∈ Finset.range T, ((r * dist x x' : ℝ) : ℂ)⁻¹ ^ j *
        stationaryPhaseConjugateOperator j (builtSymbolPairAngularAmplitude b b x x')
          (radialAngle 0 (x - x') + Real.pi))

                                                                  
                                                                     
                                                                             
                                                        
                                
                                                              
                                                          
                              
                                                        
                              
                                                     
                                            
                                                                   
                                        
                                                      
                                                                                
                                                               
                                                                                     
                 
                                                                            
                                                                       

end FalconerThetaGauge
