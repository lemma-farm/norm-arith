-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Foundation.Sobolev.Mollify.Transport

/-!
# The mollified weak-derivative identity as an explicit integral

Adapted from PDEFoundation (EllipticRegularity, 2026) with the author's
permission. Integrating the derivative of the normalized bump kernel against
`u` reproduces the mollification of a weak partial derivative of `u`, at every
point whose closed `ε`-ball lies in the domain of the weak derivative. The
result is the integral form of the transport identity, stated on its own so
that it can be used without unfolding the convolution derivative.
-/

open scoped Convolution Topology
open MeasureTheory

set_option autoImplicit false

noncomputable section

namespace CKN

                                                                                             
                                                                                           
                                                
                                                            
                                                                
                                                                 
                                                                             
                                      
                                                                         
                                                        
                                              
                                         
                                                          
                                       
                                                  
                                            
                                      
                                                                                      
                                      
                                                                       
                                        
                                                            
                                                                 
                                                                 
              
            
                                                        
                                                     
                                            
        
                                               
                       
               
            
                 
                            
                                   
                                                 
                                                      
                                       
                                    
                                                               
                                                       
                                      
                                                                      
                                                                     
                                             
              
                                                                         
                                                                          
              
                                                             
                                               
        
                    
                                                        
                                      
        
                                                        
                                                                   
            
                                                                           
                  
                                  
                                          
                                     
                                        
               
                                                                           
                  
                             
                
                                                                           
                    
                                                               
                                    
        
                                                                           
                    
                                                                 
                                      
                                             
                                
            
                                                                 
                                    
                                     
                                                                         
                                       
                                                                                   
                                                        
               
                                                             
                                     
                                            
        
                                                             
                                      
                                             
                                
                      
                             
                                                                                 
                                                      
                                       
                                             
                                
                          
              
                         
                                                                               
                                                                                   
                  
            
      
                                                                         
                  
                                                               
                                         
                                                             
                                                                           
                         
                                                            
                    
                        
                 
                                     
                                                            
                                                                          

end CKN

end
