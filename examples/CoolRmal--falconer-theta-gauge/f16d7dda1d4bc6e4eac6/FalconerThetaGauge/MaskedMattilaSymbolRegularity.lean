module

public import FalconerThetaGauge.MaskedMattilaPointwiseInversion
public import FalconerThetaGauge.ScheduledSymbolBudget
public import Mathlib
/-! # Genuine built-symbol amplitudes for the pointwise masked Mattila inversion -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function
open scoped ContDiff

namespace FalconerThetaGauge

def builtSymbolAngularAmplitude (b : Plane → UnitCircle → ℝ) (x : Plane) : ℝ → ℂ :=
  fun θ ↦ (b x (unitCircleOfAngle θ) : ℂ)

def builtSymbolPairAngularAmplitude (b₁ b₂ : Plane → UnitCircle → ℝ)
    (x y : Plane) : ℝ → ℂ := builtSymbolAngularAmplitude b₁ x * builtSymbolAngularAmplitude b₂ y

                                                                              
                                                                            
                                                                  
                                                        
                               
                                                                                      

                                                                              
                                                                             
                                                                                   
                                                          
                                                                   
                                                                             
                                                                        
                                             
                               
                                                               
                                       
                                              
                                                                      
              
                                                                  
                                      
                                                                
                                                          
                                                                             
                                                                                 

                                                                                   
                                                                          
                                                                               
                                    
                                                                   
                                                                                   
                                                                   
                                                     
                                                       
                                                             
                                                                   
                                                                 

                                                                                       
                                                                  
         
                                                                       

                                                                                 
                                                                                            
         
                                                             
                                                          
                                                                                 
     

                                                                        
                                                                 
                                    
                                                        
                                                                        
                                                                  
                                                        
                                                

end FalconerThetaGauge
