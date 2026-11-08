/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/

import QuadraticCarleson.CalderonZygmundDyadicStopping

/-!
# Converting canonical dyadic stopping cells to centered intervals

The analytic atom estimates use a center and a length, while the canonical
stopping construction uses half-open dyadic cells.  The project's centered
interval convention is also half-open, so this file supplies an exact set
identity and transfers literal pairwise disjointness without a boundary loss.
-/

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace QuadraticCarleson
namespace CalderonZygmundStoppingIntervals

open CalderonZygmundDyadicStopping

set_option autoImplicit false

noncomputable section

                                                           
                                                          
                                                                   

                                                           
                                                          
                                       

                                                             
                           
                                           

                                                                       
                 
                                                                           
                                                            
                                              
                                                        
                                                       
                  

                                                                  
                                 
                                              
                                                        
     

                                                                        
                                                        
                          
                                                            
                                       
                                                                

                                                           
                          
                                                                     
                                    
                                                    
                                                         

                                                                          
                     
                                                                
                                                              
                                                                   
               
                                                         
                                     

                                                                  
                                                                  
                                                                         
                                                                   
                                                             

                                                                             
              
                                                                          
                                                                    
                                                                          
                                                   
                                           

                                                                  
                                                                          
                                                                     
                                             
                                                        
         
      

end
end CalderonZygmundStoppingIntervals
end QuadraticCarleson
