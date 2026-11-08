-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Foundation.Parabolic.Basic

/-!
# Hölder bounds for the parabolic metric

This module names the seminorm used by the space-time regularity statements.
The measure-theoretic representative predicate records agreement on a set.
-/

open scoped ENNReal NNReal Topology

open MeasureTheory Set

set_option autoImplicit false

noncomputable section

namespace CKN.Foundation.Parabolic

def ParabolicHolderSeminormLE
    (U : Set ParabolicPoint) (g : ParabolicPoint → ℝ)
    (α K : ℝ) : Prop :=
  ∀ x ∈ U, ∀ y ∈ U,
    |g x - g y| ≤ K * parabolicDist x y ^ α

                                      
                                                     
                       
                           
                               
                                       

                                                   
                               
                                                            

namespace ParabolicHolderSeminormLE

                                                                    
                                                                     
                                        
                                          

end ParabolicHolderSeminormLE

                                                   
                                                               
                                             
                                                 
                                                  

end CKN.Foundation.Parabolic
