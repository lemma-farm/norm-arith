module

                                                                         
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-! # Explicit positive-time Kolmogorov Gaussian

The covariance is ((2t³/3,t²),(t²,2t)). The sign of the mixed term corresponds to
forward transport with velocity v, hence the adjoint operator -v∂X+∂vv.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov

/-- The Gaussian is defined only at strictly positive times. -/
abbrev BellmanPositiveTime := {t : ℝ // 0 < t}

                                                                          
                                                                        
                                                                        

                                                                   
                                                                      
                                                                                  

                                                              
                                                                          
                                 
                                                                                
                                 
                                  
      

                                   
                                                                              
                                         
                                 
                                
                                                         
                                        
                                                                     
                       
                                       
                                            

                                       
                                                                         
                                       
                              
                                                        
                                                                         
                    

                                                       
                                                                        
                                                                             
                              
                                                                        
      
                                                      
                                                        
                                                
                      

                                            
                                                                      
                                                                             

                                                                           
                                                            
                                           
                                                                                   
                                       
                                                                          
                                               

                                                                                        
                                                          
                                           
                                                                                 
                                               
                                                                    
                           
                                               

end HypoellipticAleksandrov.KineticAleksandrov
