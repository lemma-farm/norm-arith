-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Foundation.Euclidean.CZInputs
import CKN.Foundation.Euclidean.RieszSecondL2Input
import CKN.Foundation.Euclidean.LpExtensionInputCast

/-! # The completed gradient component on smooth compactly supported data

The completed `L^(6/5)` operator is built from the `L²` carrier by a
norm-controlled extension, so on data that already lies in `L²` it reproduces
the raw `L²` operator, and on smooth compactly supported data the raw operator
is the classical Hessian `∂ᵢ∂ⱼ(N * G)` of the Newtonian potential.  This is the
only place where a classical representative of the completed operator is
identified, and it is used exactly on the dense class of test data.
-/

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic

set_option autoImplicit false
noncomputable section

namespace CKN.Foundation.Euclidean

open CKN

                                                                         
                 
                                                         
                                  
                                                                           
                      
                                                             
                                                      
                                                  
                                                       
                                        
                                               
                                              
                                                                        
     

                                                                          
                                                
                                                                 
                                  
                                                                           
                      
                                                             
                                                      
                                                
                                                                       
                                       
                                                                 
                                          
                                                                 
                                                                                    
                                                                        
                                                  
            

                                                                              
                                                              
                                                            
                                  
                                                                           
                      
                                                             
                                                      
                                                
                                                                             
                                                                 
                                                          
                                                             
                                                
                                         
                                                
                                                                            
                                                                 
                                                                                 
                                                                                   
      
                                             
                                                                 
                                            
                
                                                                                       
                                                           
                
                                                                            
                                          
                   
                                                                                  

end CKN.Foundation.Euclidean
