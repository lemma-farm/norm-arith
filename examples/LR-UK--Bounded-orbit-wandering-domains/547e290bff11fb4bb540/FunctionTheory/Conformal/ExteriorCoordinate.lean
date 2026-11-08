module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Topology.Connected.Basic
public import Mathlib.Tactic

@[expose] public section

open Set Metric Complex Bornology
open scoped Topology

namespace FunctionTheory

/-- The spherical exterior in the coordinate `z ↦ 1/z`. Zero represents
infinity, so it is explicitly included. The pole belongs to the removed set. -/
def invertedExterior (K : Set ℂ) : Set ℂ := {w | w = 0 ∨ w⁻¹ ∉ K}

                                                      
                                                                  
       
             
                     
                          
                                                    
                               
                      
                                      

                                                                
                                     
                               
            
                      
           
                                                             
                                       
                                 
                                           
              
                        
                      
           
               
                                           
                                                       
                                                                   
                                                                           
                                                                      
                               
                                             
                                          
                                                                                       
                                                             

                                                                      
                                                      
                                                 
                             
            
                      
                                             
                                                             
                                              
                               
           
                         
                                                                        
                           
                                              
                         
                                       
                                                   
                                                                              
                                             

                                                                           
                                                                               
                                                
                                                                    
                                          
                                                    
                              
                  
                       
                            
                                                 
                                       
                                                
                                                                               

                                                                                  
                                                               
                                                    
                                               
          
                                                 
                                     
                                                                                      
                                              
                                       
                                                               
                                                               
                                                                                
                                                                  
                           

end FunctionTheory
