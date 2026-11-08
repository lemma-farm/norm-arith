module

public import MeyerGeneralProblem.Cardinal.Strong.RationalCoarseValue
public import Mathlib
@[expose] public section

/-! Computable exclusion data and actual binary residuals for accepted PREFIX Section 2.
Fixed constants are indices into earlier rational name programs. Their names
are inputs to this finite evaluator; the final recursive family is still unpaid.
-/

namespace MeyerGeneralProblem.StrongParity

/-- Ordinary original exclusion data, with fixed constants represented by name indices. -/
inductive ComputedRootExclusion where
  /-- An original root versus an encoded coarse value. -/
  | root (n : ℤ) (u v : ℚ)
  /-- An original label difference versus an encoded coarse value. -/
  | difference (n l : ℤ) (u v : ℚ)
  /-- An original label sum versus an encoded coarse value. -/
  | sum (n l : ℤ) (u v : ℚ)
  /-- An original root plus one earlier named constant versus another. -/
  | fixed (n : ℤ) (y gamma : ℕ)

                                                                                         
                                                                              
                             
                                                                                                    
                                               
                                                      
                                                                                       
                                                                    
                                                                                       
                                                                        
                                           

                                                                               
                                                                                 
                                            
                                                             

                                                                                 
                                                                            
                                         
                                                    

noncomputable section

                                                                                        
                                                                                                   
                              
                                              
                                
                                                          

                                             
                                             
                                       
      
                                               
                                           
                             

                                             
                                             
                                       
      
                                               
                                        
                             

                                             
                                                   
                                                   
              
          
                                                
                            
          
          

                                                                                                  
                                                                               
                                                                   
                                                                                           
                                                                           
                           
                 
                 
                                                                              
                                                     
                                                                                     
                                                
                                      
                                                          
                                 
                         
                          
                                                                                
                                                                                            
                  
                                                                                
                                                                         
                                                                                               
                                                                      
                                                                                 
                  
                                                                              
                                                                   
                                                                                             
                                                                    
                                                                               
                      
                                                                              
                                                                   
                                                                                             
                                                                               

                                                                                          
                                                                            
                                                                   
                                                                                           
                                                                               
                                                           
                                                                 
                                         
                                                                                                 
          

                                                                                             
                                                                                         
                                    
                                                                           
                                                                                                
            

                                                                                                 
                                                                                    
                                                                   
                                                                                         
                                                                                              
                                                         
                                                           
                                                        
          
                        
          

end

end MeyerGeneralProblem.StrongParity
