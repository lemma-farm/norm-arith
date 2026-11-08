module

public import FalconerThetaGauge.SpaceSplittingSeparatedCarriers
public import Mathlib
/-! # Genuine almost-everywhere finite coverage of the far comparable spatial terms -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function Finset
open scoped Classical ENNReal

namespace FalconerThetaGauge

open GaugeFrostman GaugeSeparatedMeasures

def spaceSplittingRootFourMeasure (ρ : Measure Plane) (a : ℕ) (X Y : Fin 2 → ℤ) :
    Measure ((Plane × Plane) × (Plane × Plane)) :=
  ((ρ.restrict (dyadicCube a X)).prod (ρ.restrict (dyadicCube a X))).prod
    ((ρ.restrict (dyadicCube a Y)).prod (ρ.restrict (dyadicCube a Y)))

instance (ρ : Measure Plane) [IsFiniteMeasure ρ] (a : ℕ) (X Y : Fin 2 → ℤ) :
    IsFiniteMeasure (spaceSplittingRootFourMeasure ρ a X Y) := by
  unfold spaceSplittingRootFourMeasure
  infer_instance

                                                                                       
                                                                           
                                               
                                                    

                                                              
                                                          
                                                                     
                                                               
                                                                     
                                                                   
                                                                                   

                                                                                               
                                                                            
                                                                                  
                                                
                                            
                                        
                                                                                                
                                                                
                                                                              
                      
           
                        
                                                                                    
                      
                                                                    
                              
                                                                             
                                                       
                                                                              
                                                                                  
                                                  
                                                                                        
                                                  
                                                                                        
                                                              
                                                                                    
                      
                                                
                                                                           
                                                                                         
                                                
                                                                           
                                                                                         
                                      
            
                                                                                       
                
                                                                                      
                                                                                      
                                                                               
                                 
                                                     
                                                        
                                                     
                                                        
                                                                                         
                                  
             
                                                                                 
                  
                                                                                 
                  

                                                                             
                                                                                  
                                                                                         
                                  
                                                        
                                                    
                                                         
                                 
                                                                          
                                                                                  
                                                              

                                                                                              
                                                                              
                                                                                
                                                    
                                                                
                                             
                                  
                                                   
                                                     
                     
                                                                                          
                                                                                            
                                                                                         
                              
                                  
                     
            
                                                                   
                                    

end FalconerThetaGauge
