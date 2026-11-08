/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/

import QuadraticCarleson.KrauseLaceyPositiveCorrelation
import Mathlib
/-!
# Finite central-third localization at one dyadic scale

This is the exact finite-support version of the three-shift decomposition in
KL18 (3.1).  Intervals of length `L` are chosen so that their central thirds
are the consecutive half-open tiles of length `L/3`.  Hence a compactly
supported input is exactly the sum of finitely many central-third
restrictions, with no overlap and no boundary exceptional set.

Grouping the tile index modulo three recovers the three shifted grids.  The
cross-scale nesting of each such group is left to the subsequent grid module;
the results here close the finite, fixed-scale identity used before that step.
-/

open Function MeasureTheory Set

namespace QuadraticCarleson
namespace KrauseLaceyShiftedLocalization

set_option autoImplicit false

noncomputable section

                                                                         
         
                                                                            
                                 
                                  
                               

                                                                    
                                                    
                                                   
      

                                                                          
                                                  
                                                             
                                                         
                  

                                                                          
                                                                       
                                                                                         
               
                           
                 
                                                                
                                                                
                                                     
                                          
                                          
                                                        
                                                                  
                                                  
                          
                                                  
                                                        
                                                                  
                                                  
                          
                                                  

                                                                  
                                                                              
                                                                    
                    
                                             
                          
                                       
                                          
                                                    
               
              
                                
                                           
                                  
                                          
               
               
                                          
                                
                    
                                                           
                                            
                                         
               
                 
                                                                
                                        
                                                             
                                              
                                            

                                                                          
                                                                  
                                                       
                                         
                                                 
                                                          
                                                             
                                            
           
          
                       
                                                              
                                           
                                                      
                                               
                                     
                               
                                      
                     
                                       
                                                                               
                
              
                         

                                                                         
                                                             
                                                                                 
                                      
            
                 
                                                
                                           
                                                       
                                              
                                                       
                                          

                                                                   
                                                              
                                               
                                           
                              
                               
                                          
                                                             
                                              
                                                                                 
                    
                                             
                           
                      
                                               
                                                       
                        
               
                                                 
                                              
                         
                                                 
                                                 
                                                       
             
             
           
       
                                                             
         
                             
                                                     
                                                     
                                                           
                 
                 
               
            
              
                                                                               
                                                     
                                                                            
                                                                           
                                                                              
                                                                             
                                       
                                                                  
                                                             
                                          
          
                    
                                              
                                             
                                     
                 
                                                      
                                                
                                
                 
                
                                                            
                                                      
                                
                 
                                             
                                         
                                    
                  
           
                                                              
                                                                  

                                                                      
                                       
                                                       
                              
                              
                                               
                                          
                                                             
          
                                                   
                                                                                       
                                                      
                                    
                                                                        
                                     
                                     
                         
                                            
                                                                                
      
                                               
                                                                           
                                             
                                                                
                           


end
end KrauseLaceyShiftedLocalization
end QuadraticCarleson
