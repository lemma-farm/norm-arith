module

public import FalconerThetaGauge.DirectionalTestsTube
public import Mathlib
/-! # The literal projection coincidence count of the normalized anchor restriction -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function

namespace FalconerThetaGauge

open GaugeFrostman GaugeSeparatedMeasures

/-- The actual probability restricted and normalized to the occupied anchor cell. -/
def projectionAnchorMeasure (ρ : Measure Plane) (p : ℕ) (P : Fin 2 → ℤ) : Measure Plane :=
  normalizedRestrict ρ (dyadicCube p P)

instance (ρ : Measure Plane) [SFinite ρ] (p : ℕ) (P : Fin 2 → ℤ) :
    SFinite (projectionAnchorMeasure ρ p P) := by
  unfold projectionAnchorMeasure normalizedRestrict
  infer_instance

                                                                        
                                                                                 
                                                              
                                     
                                    
                                                                           

                                                                        
                                                                                            
                                          
                                                     

                                                                           
                                                     
                                                         
                                                          
                                             
                                                       
                                                      
                                                           
                                            
          

                                                                                   
                                                                      
                                                                                  

                                                                           
                                                                                   
                                                            
                                                                           
          

                                                                                 
                                                                                       

                                                                                    
                                                                                          
                    

                                                                                        
                                                                                                
                                                                                              
                                            
                                                                                          
                                                           

                                                                                    
                                                                                
                                                  
                                                                    
                                                
         
                                                                           
                               
                                 
          

                                                                              
                                                
                                                                                      
            
                                            
                                                                        

                                                                                   
                                                                                   
                                                                                       
                                                                                          

                                                                                            
                                                                                 
                                                                                        

                                                                                  
                                                  

                                                                           
                                       
                                          
                                                    

                                                                            
                                                                                     
                                                                       
                                                                
                                                             
                                                               
                                                                              
                                          
                                                                               
                                                                           
                                                         
                                                                                    
         
                                                                                  
                                               
          
                                                                    
                                                                         
                   
                                                                  
                     

end FalconerThetaGauge
