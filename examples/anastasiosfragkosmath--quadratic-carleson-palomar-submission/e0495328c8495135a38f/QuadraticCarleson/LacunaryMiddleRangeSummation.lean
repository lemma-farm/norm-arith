/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/

import QuadraticCarleson.LacunaryMiddleRange
import QuadraticCarleson.LacunaryVerySmallRange
                                         
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Summation consequences for the lacunary middle range

The middle-range part of the paper uses three purely arithmetic facts:

* a modulation block `Q B τ` has exactly `B` integer indices;
* a frozen scale range `R B c τ` has at most `5B` indices under the paper's
  stated largeness condition;
* after restricting `τ` to one residue class modulo `10^10`, the frozen
  ranges are pairwise disjoint, so their nonnegative masses sum with no
  overlap loss.

This file packages the corresponding finite and countable sum estimates.
The last results use the author's exact half-open dyadic atom-scale partition
to turn scale coefficients back into arbitrary atom coefficients.  No
operator estimate is assumed.  The remaining analytic input in the paper is
the finite-modulation weak estimate on each `Q` block (and support vanishing
for the too-large branch of the error); those are deliberately not encoded
as arithmetic hypotheses here.
-/

open Set
open scoped ENNReal BigOperators

namespace QuadraticCarleson.LacunaryMiddleRangeSummation

open QuadraticCarleson.LacunaryMiddleRange

set_option autoImplicit false

noncomputable section

                                                                        
                                   
                                                                
                                 
                                              
      
                                            
                                                
                                             

                                                                           
                         
                                                       
                                   
                                   
                                              
      
                                                
                                                
                                           
                             
            
                                          

                                                                            
                                                 
                   
                                                            
                                                              

                                                                            
                
                                          
                                               
                  
                                      
                                        
                                             
                
               
                                                                
                                                            
                                   
                   

                                                                          
                 
                                 
                                               
                             
             
                                                                             
                                                                  
                                 
                          
                      
                  
                                                                   
               
                                                            
                           
                 
                        
                                                         
                                       
               

                                                                          
                                            
                               
                                               
                               
                                                             
      
                                           
                           
                                                                             
                      
             
                                               
                                                  
                                  
                        
               
                                               
                                   
                           
                                                                          
                       
                           
                                
             
                                                         

                                                     
                             
                                                           
                                                                           

                                                                        
                                                
                             
                             
                                                  
                       
                                                            
                      
                        
                  
         
                                                                   
                        
                            
                                                                    
              
                                                                         
              
                                                                                 
                                             
                                     

                                                                          
                                                                    
              
                                         
                             
                                               
                                                          
                       
                                                                
                         
      
                                                                
                                             
                                                                  
                                                               

end
end QuadraticCarleson.LacunaryMiddleRangeSummation
