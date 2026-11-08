-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Foundation.Parabolic.Holder
import CKN.Foundation.Parabolic.Doubling
import CKN.Foundation.Parabolic.Integration.Slice
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Covering.DensityTheorem
import Mathlib.MeasureTheory.Integral.Average

/-!
# Campanato oscillations on parabolic cylinders

The `L^p` oscillation of a function on a parabolic cylinder, the Campanato
bound it satisfies on a region, the tail constant of the dyadic geometric
series, and the comparison of the average of `|f|` on a subset with the
average on the ambient set.  The oscillations use genuine space-time averages.
-/

open scoped ENNReal NNReal Topology

open MeasureTheory MeasureTheory.Measure Set Metric Filter

set_option autoImplicit false

noncomputable section

namespace CKN.Foundation.Parabolic

                                                 
                                                               
                            
                                                                  
                                                                                    
                                              

                                  
                                                          
                                  
                                                              

                                     
                                                     
                           
                                     
                                                            

def parabolicCampanatoTailConstant (α : ℝ) : ℝ :=
  1 / (1 - (2 : ℝ) ^ (-α))

                                        
                                                   
                                           
                                       
                                       
                                
                          
                                                              
                                                               
              
                                                   
                                             
                                            
                                                                 
                    
                                                                         
                                                                         
                                                                  
                                              
                                 
                                           
      
                                         
                                              
                                           
                                     
                                                   
                

end CKN.Foundation.Parabolic
