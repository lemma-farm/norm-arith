/-
Ported from Naganori Yamaguchi, SawinTotallyRealTowers, commit
3a455e1aa9140dbbe7b7d68f508392a69c86d0f4, under Apache-2.0.
Modified: project-local imports relocated; Lean 4.32 compatibility changes
are recorded in third-party/yamaguchi/compatibility.patch.
Original declaration namespaces and mathematical statements are retained.
-/

module

public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.DiscreteValuationField.ValuationSubringUnits.RangeRestrictedTopology
public import Mathlib
@[expose] public section
set_option backward.privateInPublic true


set_option autoImplicit false

/-!
# Multiplicative-range restriction for local fields

This file packages range restriction as a `LocalField` and exposes the
properness and completeness of the resulting topology.
-/

noncomputable section

universe u v

open scoped Valued

namespace LocalFieldTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField

namespace LocalField

variable {K : Type u} [Field K]

                                                                            
                        
                                              
                             
                                 
                                                                                                   
                                     
                                                    
                                                             
                              
                                                                                                              
                              

                                                                                 
                                  
                               
                   
                         
                                                           
                                                                                                
                                       
                                                                                                                  
                       
       
                                                                                                                           

                                                                                   
                                    
                               
                   
                         
                                                           
                                                                                                
                                       
                                                                                                                  
                         
       
                                                                                                                             


end LocalField
end LocalFieldTheory.DiscreteValuationField

end
