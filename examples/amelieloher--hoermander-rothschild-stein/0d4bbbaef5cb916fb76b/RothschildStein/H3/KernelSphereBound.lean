-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.PositiveType

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set
namespace RothschildStein.H3
open G2
variable {N : ℕ} {G : HomogeneousGroup N}

/-- The order-zero kernel seminorm is the actual unit-sphere maximum
Λ_{T,0} (BB Definition 8.13 and (8.7), p. 346). -/
def kernelSphereBound (ν T : (Fin N → ℝ) → ℝ) : ℝ :=
  sSup ((fun x => |T x|) '' {x | ν x = 1})

                                                                    
                                                         
                                                         
                                                                                     
                               
                                                    
                                                
                                                      
                                                                 
                                                                  
                             
                         
                 
                                                                    
         
                                   

end RothschildStein.H3
