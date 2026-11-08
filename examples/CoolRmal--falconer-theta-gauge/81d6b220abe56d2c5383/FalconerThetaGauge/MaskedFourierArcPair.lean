module

public import FalconerThetaGauge.MaskedFourierRadialMeasure
public import FalconerThetaGauge.EqualArcCutoff
public import FalconerThetaGauge.FiniteGraphSchurIntegral
public import Mathlib
/-! # Actual square-root arc amplitudes in the finite joint Fourier measure -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function

namespace FalconerThetaGauge

/-- The actual radial and two-circle product measure, with no hypothetical energy input. -/
def maskedFourierJointMeasure (K v : ℕ) : Measure (ℝ × UnitCircle × UnitCircle) :=
  (maskedFourierRadialMeasure K v).prod (circleArcLength.prod circleArcLength)

instance isFiniteMeasure_maskedFourierJointMeasure (K v : ℕ) :
    IsFiniteMeasure (maskedFourierJointMeasure K v) := by
  unfold maskedFourierJointMeasure
  infer_instance

                                                                               
                                                                           
                                                    
                                                                                  
                                            
                                                        
                                              
                                              

                                                                                       
                                                                 
                                                                             
                                                                   
                                                               
                                                   
                                                             
                                                                                          
                                                
                                                     
                                                     
      

           
                                                                        
                                               
                                                                    
                                                                
                                           
                                                                            
                                                             
                                                
                                            
                                                
                                                             
                                                
                                            
                                                
                                                              
                                                  
                                                     
                                                                  
                                                              
                                                  
                                                     
                                                                  
                                                    

                                                                     
                                                               
                                                                    
                                                                   
                                                                
                                                                             
                                                               
                                 
                                                         
                                                            
                                                         
                                                            
                                                    
                                                      
                                                                                  
                                                                                          
                                       
      
                                    
                               
                                                                  
                                      
                                                                                  
                       
                    

                                                                   
                                                               
                                                                    
                                                                   
                                                                  
                                           
                                                                   
                                        
                
                                                                                              
                                                        
                                                                                         

end FalconerThetaGauge
