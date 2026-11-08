module

public import FalconerThetaGauge.MaskedFourierEnergyCutoff
public import FalconerThetaGauge.LinearPhase
public import Mathlib
/-! # The literal source radial amplitude and its compact dyadic support -/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ContDiff

namespace FalconerThetaGauge

/-- The actual radial weight `2⁻ᵛ Ψ(r/2ᵛ) r²` in Estimate 7.6. -/
def orthogonalityRadialAmplitude (K v : ℕ) (r : ℝ) : ℂ :=
  (((2 : ℝ) ^ v)⁻¹ : ℂ) * (maskedFrequencyCutoff K (r / (2 : ℝ) ^ v) : ℂ) * (r : ℂ) ^ 2

                                                         
                                                         
                                     
                                                            
                                                                             
                                        

                                                              
                                                        
                                                
                                            
                                                   
            
            
               
                                        
              
                                    
                                                                                
                                            

                                                                
                                                 
                                                   
                                           
            
                
                                                          

                                                                  
                                                           
                                                  
                                               

                                                                   
                                                                                     
                                            
                                                                                             
                                  
                                                                                        
                             

                                                                         
                                               
                                                                                 
                                                          
                                                           
                                                            
                                                                        
                                                  
      
                                               
                                                                     
                                                 
                                                                                              
                                                                                   

end FalconerThetaGauge
