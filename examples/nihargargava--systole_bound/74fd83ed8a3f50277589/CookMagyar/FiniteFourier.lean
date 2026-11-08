module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Mathlib.Analysis.Fourier.ZMod
public import Mathlib.Tactic

@[expose] public section

open scoped BigOperators

namespace SystolicGrowth
namespace CookMagyarFiniteFourier

/-! # Finite Fourier expansion of the local cubic count

This file proves the exact finite-group identity underlying the local factors
in the Cook--Magyar circle method.  It contains no analytic estimate.
-/

variable {q : ℕ} [NeZero q]

/-- The reduction modulo `q` of the polynomial `X³ - X`. -/
def cubicResidue (x : ZMod q) : ZMod q := x ^ 3 - x

                                                                                
                                                            
                                  

                                                                     
                    
                                                      
                                                                                     

                                                           
noncomputable abbrev standardAdditiveCharacter : AddChar (ZMod q) ℂ :=
  ZMod.stdAddChar

                                                                           
                                                             
                  
                                                             

                                                           
                                                        
                                                     
                                        
                                                    
                                    
                                    

                                                                     
                      
                                          
                                                
           
                            
                                                
                                                      
           
                                              
                   
                          
                                                        
                                     
                             

                                                   
                                          
                                   
                                          
                                                          
                                      
         
                                          

                                                              
                                                       
                                   
                                          
                                              
                                                                
                                                            
         
      

                                                                            
                                                                          
                                           
                                                          
                          
                  
                                       
                                                 
                                                      
           
      
                  
                                       
                                                 
                                              
                                         
                                                
                                                        
                                    
                     
                                                                       
                                              
                                                                    
                              
                                    
                     
                                    
                     
                                                            
                                
                                                         
                                    
                     
                                        
                                                                    
                                                        
                                       
                                         
                             
                                    
                     
                            

                          
                                                                        
                                                                       
                          
                                                  
                          
                                      
                 
                     
                                         
                                                      
                                                         
                             
                                
           

end CookMagyarFiniteFourier
end SystolicGrowth
