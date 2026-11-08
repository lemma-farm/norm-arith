-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

module

public import AVenhance.Statements.Construction.StreamVel
public import AVenhance.Statements.Construction.IsStreamSeq
public import AVenhance.Infra.Ingredients.EpsilonConsequences
public import Mathlib

/-! Conditional hypotheses for the limit-field argument in §2.

`StreamRegularityBounds` is exactly the three estimates in the first part of the stream-regularity estimates:
the increment estimate at every order, the estimate on `Φ m` for `n ≥ 2`,
and the low-order estimate on `Φ m` for `n ≤ 1`.  It is data, not an import
of the draft theorem.  `StreamVelocityTimeIncrementBound` isolates the one
additional quantitative input used below for temporal Hölder continuity; it
is the mean-value consequence of the estimate obtained by differentiating
the recursion in (e.psi.recursion.partial.t).
-/

@[expose] public section

open MeasureTheory Homogenization Filter Topology

noncomputable section

namespace AVenhance

                                                                                                                
                                                             
             
                                                              
                                     
                           
             
                                                                     
                                                    
                     
                                                       
                                                                 
                                                     
                     
                                                   
                                                 

                                                                                          
                          
                                                                     

                                                                            
                                    
                                                                       
                        
         
              
                                         
                                        
                                                                           
                                          
                                                                   
                                                            
                                
             
                                                            
                                                                 
                                                                     
                                 
                                  
                              
                               

                                                                          
                                            
                

                                                                                         
                                                                            
       
                                                        
                                    
                                            
                        
                                                          
                                                                                 
                
                                                       
                                                           
            
                                                                                   

                                                                                     
                       
                                                                                 
                             
                                            
                                                             
                                                                 
                                                                                
                                                  
                          
                                                                
                       
             
              
                       
             
              
                                      
                   
                                                                             
                                             
                                                                   
                                    
                           
                                                                                        
                          
                                                             
        
                                  
                               
                                                                                            
                                                        
                                                             
                               
                                     
                                               
                                                        
                                           
              
                  
                                                      
                                                         
                                                             
                                                            
                                     
            
                                                              
                                                                   
                                                    
                                                               
                                                                   
                                                       
             
                                              
                                        
                                                                               
                                             
                                                                        
         
                                

                                                                              
                                                      
                                                                                
                                                           
                                            
                                                           
          

                                                                         
                                                                                  
theorem streamSeq_isAdmissible {β : ℝ} {I : Ingredients β}
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hseq : IsStreamSeq I Φ) :
    ∀ m, IsAdmissibleStream (Φ m) := by
  intro m
  cases m with
  | zero =>
      rw [hseq.1]
      constructor
      · fun_prop
      · intro n k t x
        simp
  | succ m =>
      obtain ⟨hm, _⟩ := hseq.2 (m + 2) (by omega)
      simpa using hm

                                                                             
                                                    
                                                       
                                              
                                                              
                                     
                                                                     
                    

                                                                                          
                                                            
                                                                   
                                                    
                                                                                    
                                                              
                                          
                                    
                                                                                                                       
                                                               
                                                         
                                
                                                               
                        

                                                                          
                        
                                                                               
                                                    
                                                                      
                             
                                                     
                                           
                                          
                              
                          
                                                                     
                                                
                                           
                                    
                                                                                                                       
                                                               
                                           
                                                                                      
                                                                                 
                                           
                                    
        
                                   
                                                      
                                                                       
                                                 
                                           
        
                                  
                                                                 
                                                     
                                                  
                                                                  
             
             
                            
            
                     
                      

                                                                         
                                                                   
                                                                               
                                                    
                                                                      
                                     
                                               
                                    
                                              
                                          
                              
                          
                                                                     
                                                
                                           
                                    
                                                                                                                       
                                                               
                                           
                                                                     
                                                                      
                                                                  
                                                                                
                                         
                                                            
        
                                  
                                                                 
                                            
                                        
                                               
                                              
                              
                                                             
                                
             
             
                                   
                    
            
                         

                                                                             
                                                                          
                                                                 
                                                                        
                                     
                                          
                                                        
                                                            
                                             

end AVenhance
