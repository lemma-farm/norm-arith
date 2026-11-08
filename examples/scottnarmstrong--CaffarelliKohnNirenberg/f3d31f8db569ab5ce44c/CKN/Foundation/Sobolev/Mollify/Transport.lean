-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Foundation.Sobolev.Mollify.Basic

/-!
# Interior transport of weak derivatives through mollification

Adapted from PDEFoundation (EllipticRegularity, 2026) with the author's
permission. The translated `ContDiffBump` is used as the test function in the
defining weak-derivative identity, while Mathlib supplies the convolution
derivative and measure-preserving change of variables.

The transport theorem below is pointwise on a closed-ball interior condition,
with a compact-set wrapper. The general local `L^p` approximation theorem is
not asserted here because the available Mathlib API does not provide the
needed local convolution bound and translation-continuity package.
-/

open scoped Convolution Topology
open MeasureTheory

namespace CKN

                                                          
                                            
                                                                                  
                                                   
                                                                 
                                                  
                                                                        
                                              
                                         
                                                          
                                       
                                                  
                                            
                                      
                                                                                      
                                      
                                                                       
                                        
                                                            
                                                                 
                                                                 
              
            
                                                        
                                                     
                                            
        
                                               
                       
               
            
                 
                                                                                    
                                                                              
                                            
                                 
                                                                       
                                                                      
                                                                                 
           
                                                                       
                                                                     
                                                  
                                                          
                          
                                                        
                                                                 
                                                                                
                                                                
                                                                                 
                                                                              
                
                                                       
                            
                                   
                                                 
                                                      
                                       
                                    
                                                               
                                                       
                                      
                                                                      
                                                                     
                                             
              
                                                                         
                                                                          
              
                                                             
                                               
        
                    
                                                        
                                      
        
                                                        
                                                                   
            
                                                                           
                  
                                  
                                          
                                     
                                        
               
                                                                           
                  
                             
                
                                                                           
                    
                                                               
                                    
        
                                                                           
                    
                                                                 
                                      
                                             
                                
            
                                                                 
                                    
                                     
                                                                         
                                       
                                                                                   
                                                        
               
                                                             
                                     
                                            
        
                                                             
                                      
                                             
                                
                      
                             
                                                                                 
                                                      
                                       
                                             
                                
                          
      
                                                                         
                  
                                                               
                                         
                                                             
                                                                           
                         
                                                            
                    
                        
                 
                                     
                                                            
                                                                          

                                            
                                                                 
                                                                                  
                                                     
                                                                 
                                                                        
                                                                        
                                                          
                                

end CKN
