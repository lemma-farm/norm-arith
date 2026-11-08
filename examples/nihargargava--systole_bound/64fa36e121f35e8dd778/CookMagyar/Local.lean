module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
                                     
public import Mathlib.Combinatorics.Additive.CauchyDavenport
public import Mathlib.FieldTheory.Finite.Basic

@[expose] public section

open Polynomial
open scoped Pointwise

namespace SystolicGrowth
namespace CookMagyarLocal

/-! # Local solubility of the cubic `x ^ 3 - x`

This file proves the local-solubility statement used in the singular-series
argument.  If `q >= 5` is prime, every residue modulo `q` is a sum of four
values `x ^ 3 - x`, with all four inputs nonzero.

For `q >= 13`, the proof combines the degree-three bound for the image of a
polynomial over a finite field with Cauchy--Davenport.  The remaining prime
moduli `5`, `7`, and `11` are closed finite computations evaluated by Lean's
kernel.
-/

/-- The cubic map on a residue ring. -/
def cubicResidue {q : ℕ} (x : ZMod q) : ZMod q := x ^ 3 - x

                                                                     
                                                              
                                          

                                                                        
                                                                             
                           

                                                                         
                                
                                                                          
                                                               
                             
       
             
            
                                                            
                                                          
            
                                                    
                       
             
                                      
                                                           
                                                   

                                                     
                                                          
                                              

                                                           
                                                                
                                                      

                                                                          
                                
                                                                         
                                             
                             
                                                        
                                 
                                                                
                                                
                                                     
                   
            
                                                              
                                                           
                                 
                                                                   
                                                
               
                                                                                   
                                  
                                                     
                            
               
                                
                                             
             

                                                  
                                                                     
                                         
                             
                                           
                                                           

                                                                           
                                  
                                                              
                                    
                                                   
                                                                         
                             
                                                 
                                                                 
                                          
                                                                  
                                               
                                                  
                                   
                                               
                                           
                                                
                                           
                    
           
                                                                           
                                                               
                    
           
                                                  
                                                              
                 
                              
                                                  
                           
                                               
                                                         
                
                                     

                                                                    
                                                                 
                         
                                       
                                         
                                               

                                
                                                      
                                                   
                                                                         
        

                                
                                                       
                                                   
                                                                         
        

                                
                                                        
                                                     
                                                                           
        

                                                                          
                                                                            
          
                                                                          
                                                           
                                 
             
                                                     
                                                                           
                                          
                      
                                                  
                      
                                                   
                      
                      
                      
                                                    
                      
                                                       
                                                 
                                                    
                        
                                       
                
                             
                                                      
                                                         
                                                         
                                                            
                                                            
                                                            
                                                            
                                                 
                        
      

end CookMagyarLocal
end SystolicGrowth
