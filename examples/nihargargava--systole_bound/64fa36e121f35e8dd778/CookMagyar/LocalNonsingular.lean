module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import CookMagyar.Local

@[expose] public section

open scoped BigOperators

namespace SystolicGrowth
namespace CookMagyarLocal

/-! # Nonsingular local solutions

The four-variable local-solubility theorem supplies the nonzero coordinates.
For five or more variables, an additional coordinate equal to `1` both leaves
the equation unchanged and makes the solution nonsingular: `1 ^ 3 - 1 = 0`,
whereas the derivative at `1` is `2`.
-/

/-- The derivative of the cubic map `x ↦ x ^ 3 - x`. -/
def cubicDerivative {q : ℕ} (x : ZMod q) : ZMod q :=
  3 * x ^ 2 - 1

                                                                            
                                                                      
                                                                   
                             
                                         
      

                                                                              
                                                              
                                         
                        
                                               
                                      
                                     
                                            
                                                    
                                                  

                                                                               
                                                           
                                          
                                                                      
                              
                  
             
                                                              
                                                      
       

                                                                        
                                   
                                                         
                                                              
                                             
                                    
                    
           
                                      
                      
                                         
                
                          
                                                
                   
                  
                                               

                                                                     
                          
                                                                         
                                                                 
                             
                                                    
                                                   
                               
                                                                                
           
                  
                      
                  
                     
    
           
                                               
                                                                  
                                                                  
                                                                  
                                                                       
                                                                      
                        
                                                   
                  
                                                       

                                                                           
                                                                        
                              
                                                                             
                                
                                                  
                                              
                                                       
                    
                               
                                 

end CookMagyarLocal
end SystolicGrowth
