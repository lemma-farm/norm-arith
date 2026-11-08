module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.SingularGreenCutoffsLineWeak
                                                                                                  
import Mathlib.Analysis.Normed.Operator.Bilinear

/-! # Literal first and second parameter jets of position convolution -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov Set MeasureTheory Filter
open scoped Topology

/-- The scalar position projection used by the parameter jets. -/
def barrierPositionProjection : (ℝ × ℝ) →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ ℝ

/-- The scalar velocity projection used by the parameter jets. -/
def barrierVelocityProjection : (ℝ × ℝ) →L[ℝ] ℝ := ContinuousLinearMap.snd ℝ ℝ ℝ

                                                                                      
                                                               
                                                                                

                                                                   
                                                         
                                            
                                                                                         
                                                                      

                                                                                                 
                                                               
                                                            
                                                                      
                                                                                
                                                                      
                                                                               
                                                                                    
                               

                                                                                  
                                                                 
                                                                           
                                                                      
                                                                  
                                                                                 
                                                                                       
                 
                                                                     
                                                        
                                                            
                                                 

                                                                                             
                                                                    
                                                                           
                                                         
                                                                   
                                                                                 
                                                          
                                                                            
                                                                         

                                                                                 
                                                                               
                                                                          
                                      
                                                                
                                               
                                                                                        
                                                     
                                                        
                    
       
                                 
           
                                                                                      
        

                                                                                    
                                                                         
                                                                          
                                      
                                                          
                                                     
                                                                                        
                                                     
                                                                                     
                                                     
                                               
                                                   
                                                                    
                                                       
                    
       
                                 
           
                                 
           
                                                                                            
        

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
