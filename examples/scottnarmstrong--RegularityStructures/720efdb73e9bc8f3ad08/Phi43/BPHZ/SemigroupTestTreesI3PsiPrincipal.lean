/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.SemigroupTestTreesSlab
public import Phi43.BPHZ.SemigroupTestTreesI3PsiChain
public import Phi43.BPHZ.TreeI3PsiDiagramUniform

/-!
# The principal diagram of `I(Ψ³)Ψ`, for arbitrary `z, z'`

Without Hölder gains (these need `s(z), s(z') ≤ 1`) the principal diagram
`∫∫ δK(z, w) δK(z', v) Q(w - v)³` is bounded by absolute values:
`∫ s₃(z', 0; v) s₃(w; v) dv ≤ C (s₁(z'; w) + s₁(0; w))` (total order `6`), and the `w`-integral of
`s₃(z, 0; w) (s₁(z'; w) + s₁(0; w))` over the slab `|w.1| ≤ T` is bounded by `C (1 + T)`
uniformly in the centres (`singularIntLe_slab_singularPow`).
-/

public section

open MeasureTheory Set

namespace RegularityStructures

                                                        
                                          
                                                                                 
                                                                      
                         
                                                                    
                                                      
                                                                
                                                                            
                                                            
                                                      
                                                                                        
                                                                         
                                    
                                  
                                                              
                                                                                                   
                                                                      
                                                                       
                                                                                             
                                            
                                                                              
                                                                                     
                      
                                                                               
                                                                                         
                                                                                               
                                                                              
                                                                   
                                                                                               
           
                                                                     
                                                                     
                                                                              
                                                                   
                                                                                               
                                                                                   
                                                                                           
                                                                                        
                                                     
                         
                                                   
                                                                                       
                                                                                       
                                                                                       
                                                                                       
                                                  
                               
                                                        
                                                      
                                                                                        
                                                                                                   
                                                                                                    
                    
                                
                                                          
                                                           
                                                                 
                                                                  
                                                                        
                                                                          
                         
                           
                                                          
                                                                                       
                                                                                                 
                            
                           
                                                                     
                                                
               
                                           
                                                                                            
                                                                                                 
                        
                       
                        
                                                   
                           
                
                     
                                                                                  
                                                                                                
                                                                         
                                                                   
                                     
           
                                                                           
                                                                                      
                                  
                                 
                                 
                  
        
                                                                                      
                                                       
          
      

                                                                                          
           
                                                          
                                                            
                                                                                       
                                                             
                                                                                       
                         
                                                                                    
                                                                                  
                                                          
                                        
                                  
                                        
                                                                                                  
                         
            
                                                                            
                                                       
                                                                                                
                                                                                      
                                                      
                                                                             
                                                            
                                                                             
                                                                                   
                                                                                         
                                                                                           
                                   
                                                                                      
                                              
                                                                              
                             
                                    
            
                                 
                                   
                                    
                                                                  
                                                                                        
                                                                   
                                                                                        
                                                                                 
                                                         
                                                                                           
                                                                                        
                            
                                    
                             
          
                                                                                
                                                  
                             
                     
                         
                
                                             
      

end RegularityStructures

end
