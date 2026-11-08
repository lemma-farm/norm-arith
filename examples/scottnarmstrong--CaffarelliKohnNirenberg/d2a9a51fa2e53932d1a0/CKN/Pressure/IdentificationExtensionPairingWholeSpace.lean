-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Pressure.IdentificationExtensionPairingExterior
import CKN.Pressure.IdentificationExtensionPairingSlice
import CKN.Pressure.IdentificationWholeSpace

/-!
# The whole-space distributional identity for the leading pressure term

The localized identity for `p₁` tests against spatial test functions supported in
the solution domain.  Splitting an arbitrary compactly supported smooth test
function `ψ` with an auxiliary cut-off `χ` that equals one on a neighbourhood of
`tsupport η` and is supported in the domain writes `ψ = χψ + (1 - χ)ψ`: the first
piece is admissible for the localized identity, and the second piece vanishes on
a neighbourhood of `tsupport η`, so both sides of the identity vanish on it.
The result is the identity tested against every compactly supported smooth `ψ`,
which is the form the Liouville identification consumes.
-/

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic

set_option autoImplicit false
noncomputable section

namespace CKN

                                                                                 
                                                                          
                             
                                                            
                                                      
                                   
                                                                    
                                                                
                                      
                                                       
                                      
                                                        
                                                     
                                                                                     
                                                                  
                                                  
                               
             
            
             
              
                                          

                                                                      
                                                                             
                                              
                                         
                                                            
          
                                                        
                                     

                                                                             
                                                                            
                                                           
                                            
                                                     
                                               
                         
            
                        
                                                                    
                                                                      

                                                               
                                                                                 
                                             
                                             
                                                       
                                                                                
                                                                                  
                                               
                              
                               
                                           

                                                                                
                                               
                                                                           
                                                      
                                     
                                                                           
                                                                             
                                                                         
                                       
                                                         
                                                                              
             
                           
                                                                        
                                                                        
                                
                                                                           
                                                                                  
                       
                                                                          
                                                 
                                                                 
                                                                        
           
                                       
                                                                       
                              
                                     
                                                                     
                         

                                                                                
                                                                          
                                                                              
                                                                              
                                               
                                      
                                                                    
                                                        
                                                            
                                               
                                                                     
                                                                             
                            
                                                            
                                                             
                                   
                                                  
                                                                
                                                                         
                                                              
                           
                                                         
                                                          
                                                                                
                                                                       
                                                               
                                            
        
                                                        
                                
              
                 
                                                                          
            
        
                                              
                                                      
                                                                  
           
                                                      
                        
              
                                                              
                                                     
                                                                 
               
                                                     
                        
              
                                                                                 
                 
                                                                   
                                               
                                                                    
                                                                         
                                                                                
                                                                           
                    
                  
                                  
                                                       
                                                        
                                                                  
                                                                               
                                      
                                                                      
                                                       
                                                                    
                                     
                                                            
                                                                            
                                  
                                                            
                                    
                                                                      
             
               
          
                                                                          
                                                                             
        
                                                                   
                             
                                                           
                                                           
                                                                            
                              
                                                         
                                                          
                                                         
                                                                    
             
                                   
                                               
                                   
                                               
                   
          
                                                                          
                                
                                                                         
                                                                          
                 
        
                 
          

end CKN

end
