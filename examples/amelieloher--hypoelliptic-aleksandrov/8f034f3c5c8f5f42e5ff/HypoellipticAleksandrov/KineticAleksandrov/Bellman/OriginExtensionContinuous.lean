module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.OriginJetsBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-! # The continuous zero extension of a positive-degree Bellman function -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open Set Filter
open scoped Topology

/-- Extend the punctured homogeneous function by its forced value zero at the origin. -/
def bellmanOriginExtension (phi : (ℝ × ℝ) → ℝ) (q : ℝ × ℝ) : ℝ :=
  if q = (0, 0) then 0 else phi q

                                           
                                                         
                                                            

                                                          
                                                         
                                                                
                             

                                                                                    
                                                                    
                                                                               
                                                 
                                              
                           
                                                                       
                            
                                                    
                                                                      
                                                  
                    
                                       
         
                          
           
                                                  
                                                
                                                                                  
                                                                           
                                                                                              
                                                      
                                                                                      
                                                     
                                                                              
                          
                                                                
                         
                  
                                                          
                                                                       
                                              
                                                                                              

end HypoellipticAleksandrov.KineticAleksandrov
