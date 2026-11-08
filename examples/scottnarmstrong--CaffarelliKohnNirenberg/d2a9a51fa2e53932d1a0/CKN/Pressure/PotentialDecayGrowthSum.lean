-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Foundation.Harmonic.Liouville

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic
set_option autoImplicit false
noncomputable section
namespace CKN

/-!
# Growth bookkeeping for local `L^{3/2}` norms of pressure potentials

This file collects the elementary measure-theoretic bookkeeping used to
compare the local `L^{3/2}` norms of the pressure potentials on the round
balls `euclideanBall 0 ρ`: a global `MemLp` bound restricts to any ball, the
local norm is controlled by the global norm times the linear growth factor
`1 + ρ`, and the operation of adding, subtracting, or summing finitely many
potentials preserves an affine growth bound of the shape `C * (1 + ρ)`.
The statements are purely about `MeasureTheory.lpNorm`; no analysis enters.
-/

                                                                         
                                                                            
              
                                                          
                                                                
                                        
                                                       
               

                                                                            
                                                                       
                                                              
                                                                             
                                         
                                                        
                                                                  
                                                     
                                                      
                                                      
                                                   
                                                    
                                                      
                                                        
                                           
                                                     
                                            
                                                      
                                                             
                                                                 
                                                                    

                                                                          
                                                                              
                                                      
                                                                               
                                                                            
                                                                     
                                                     
                        
                                                               

                                                                            
                                                                            
                                                                  
                                                                  
                                                     
                                                                
                                                                   
                                                                
                                                                   
                          
                                               
                                                                              
                                                       
                                         
                                                  
                                                      
                                             
                                                          
                                             
                                                           
                                      
                                                                   
                                    

                                                                            
                                                                            
                                                                  
                                                                  
                                                     
                                                                
                                                                   
                                                                
                                                                   
                          
                                               
                                                                              
                                                       
                                         
                                                  
                                                      
                                             
                                                          
                                             
                                                           
                                      
                                                                   
                                    

                                                                         
                                                                                 
                                                                  
                                  
                                                                              
                                                     
                                                                             
                                                                     
                          
                                                      
                                                                                     
                                                       
                                         
                                                         
                                                      
                                                          
                                                           
                                                      
                                                                              
                                                          

end CKN
