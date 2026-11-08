-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Core.Endgame.OneSidedGeometry
import CKN.Foundation.Parabolic.Morrey.Basic

/-!
# One-sided transfer of scalar Morrey estimates

This is Step 2 of the proof of `thm:A`, isolated as a statement about one
scalar function. The manuscript's Step 2 replaces the centre shift of
`lem:step2-morrey-balls`, which moves a centre forward in time by the square
of the radius, by a truncated shift that stops at the top face `t = 0`; see
`truncatedCylinderCenter`. Small cylinders are then covered by a cylinder of
twice the radius about an admissible centre, and the decay hypothesis
`eq:thmA-morrey` applies there. Large cylinders are paid for by the total
integral on the fixed intermediate cylinder, which is the manuscript's
unchanged large-radius case.

`oneSidedMorreyBound P τ ρ₀ A B` is the resulting constant. `A` is the
small-cell growth coefficient and `B` the total integral; the two enter
through the two regimes just described.
-/

open Set MeasureTheory
open scoped ENNReal
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Morrey

set_option autoImplicit false

noncomputable section

namespace CKN.Core.Endgame

                                                  
                                                                        
                                                           
                                                 
                                                                             
                                                              
                                                           
            
                       
                                     
                                                                       
                                    
                                                         
                                               

                                       
                                                 
                                                          
                                         
                                                   
                                                
                                                                  
                                                               
                                                                        
        
                                                                             
                 
                                                                      
                                                              
               
            
                                                                
                                                          
                                                              
                                                               
                    
      
                                                       
                                                                         
                                                      
                             
                                            

                                                                        
                   
                                                           
                                                                    
                                                                          

                                                                 
                                  
                             
                                            
                                            
                              
             
                                                                  
                                                      
                                                  
                                                                      

                                                                    
                                                                 
                                                                        
                                    
                                                     
                               
                                   
                                             
                            
                                                           
                                                               
                                                   
                                                         
                                      
                                                                     
                                          
                                                     
                                          
                                                                  
                                                 
                                                                
                              
                                                             
                                                             
                   
                                             
                                                                              
                                 
                                                             
                                                            
                                                        
                
                                                                   
                                             
                                                                      
                                                       
                                                                    
                                                                    
                    
                                       
            
                                                                            
                                                  
                                                                   
                                                                                       
                     
                                                                 
                                                                               
                                                                                                   
                    
                                                      
                           
                                                                     
                
                                                                 
                                                                   
                                                                  
                                         
                                                                 
                                                           
                                                         
                      
                             
                                                                    
                            

                                                                                      
                                         
                             
                                             
                            
                                                           
                                                               
                                                   
                                                               
                                      
                                                                           
                                       
                                                                  
                                                           

end CKN.Core.Endgame
