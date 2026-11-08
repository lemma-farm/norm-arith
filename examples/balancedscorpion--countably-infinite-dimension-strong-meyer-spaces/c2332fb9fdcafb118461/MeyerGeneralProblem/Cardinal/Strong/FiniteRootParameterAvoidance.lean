module

public import MeyerGeneralProblem.Cardinal.Strong.OriginalRootParameterExclusions
public import Mathlib

@[expose] public section

/-! A rational center avoiding EVERY equation in any actual finite PREFIX exclusion list. -/

namespace MeyerGeneralProblem.StrongParity

open Filter Set
open scoped Topology

noncomputable section

                                                                                       
                                                                          
                                                                 
                                                      
                                                                         
                                                                                
                                                              
                                                                        
                                                                 
                                             
                                                    
             
             
                                                                   
                                              
            
                                                               

                                                                              
                                        
                                                 

                                                                                                   
             

                                                                 
                                                                                       
inductive OriginalRootExclusion where
  /-- One original root avoids the encoded rational coarse value. -/
  | root (n : ℤ) (u v : ℚ)
  /-- A distinct-label original difference avoids the encoded rational coarse value. -/
  | difference (n l : ℤ) (u v : ℚ)
  /-- Any original sum, including a self-sum, avoids the encoded rational coarse value. -/
  | sum (n l : ℤ) (u v : ℚ)
  /-- An original root plus a previously fixed constant avoids a fixed real value. -/
  | fixed (n : ℤ) (y gamma : ℝ)

                                                                                                    
                                                                          
                                                                               
                             
                                                                                            
                             
                                                                                          
                             
                                                                      

                                                                                                        
                                                                     
                                                                     
                                               
                 
                 
                                                                    
                                                                                            
                         
                          
                                                  
                                                                                        
                                                                                                   
                  
                                                                    
                                                                                             
                      
                                                                    
                                                                                      

                                                                                                     
                                                                            
                                                                      
                                                 
                                                                              
                                                   
                                                    
                                                                      

end

end MeyerGeneralProblem.StrongParity
