/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Dynamics.Accelerated
public import WordCertDensity.Words.Algebra
import Mathlib.Tactic.NormNum

/-!
# Physical inverse histories

A word is listed from the root outward. Each link has positive odd integer
endpoints and the exact equation `3 * child + 1 = 2 ^ k * parent`.
The chronological forward path traverses the letters in reverse order.
Single-history charge does not assert uniqueness after grouping histories.
-/

@[expose] public section

namespace WordCertDensity

/-- Actual positive odd inverse trajectories, in root-to-source prefix order. -/
inductive PhysicalHistory : ValuationWord → ℕ → ℕ → Prop
  /-- The empty history stays at its positive odd root. -/
  | nil (root : ℕ) (hpos : 0 < root) (hodd : Odd root) : PhysicalHistory [] root root
  /-- An outer inverse block followed by its remaining inner history. -/
  | cons {k : ℕ+} {w : ValuationWord} {root child source : ℕ}
      (hpos : 0 < root) (hodd : Odd root)
      (hblock : 3 * child + 1 = 2 ^ (k : ℕ) * root)
      (tail : PhysicalHistory w child source) : PhysicalHistory (k :: w) root source

namespace PhysicalHistory

                                              
                                                      
                                                        
              
                              
                                 

                                          
                                                      
                                                        
              
                              
                                 

                                                
                                                        
                                                          
                  
                              
                               

                                            
                                                        
                                                          
                  
                              
                               

                                                                                 
                                                             
                                                                                 
                                              
                   
                   
                                                                     

                                                                                       
                                                                 
                                                                                          
                  
              
                              
                                                             
                                                          

                                                                                       
                                                                   
                                         
                                                                                       
                  
              
                                 
                                                                                 
                                                               
          

                                                                                        
                                                       
                                                                                    
                  
              
                                 
                                                                  
                                                             
                                                                
                                                                                

                                                                    
                                                         
                                                                              
                  
              
                                             
                                       
                                                                      
                             
                                                                  
                                      

                                                                                 
                                                       
                                                                                        
                                               

                                                           
                                                                
                                                                                 
                       
                                                         

                                                           
                                                                    
                                                                                 
                           
                                                                     
                                                                 
                                                             

                                                                              
                                                    
                                                                          
                                           

                                                                                      
                                                               
                                                                              
                                                                         
                                                

end PhysicalHistory

end WordCertDensity
