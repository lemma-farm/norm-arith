/-
Ported from Naganori Yamaguchi, SawinTotallyRealTowers, commit
3a455e1aa9140dbbe7b7d68f508392a69c86d0f4, under Apache-2.0.
Modified: project-local imports relocated; Lean 4.32 compatibility changes
are recorded in third-party/yamaguchi/compatibility.patch. The Mathlib
4.35 Denumerable import relocation is recorded in
third-party/yamaguchi/lean-v4.35-migration.patch.
Original declaration namespaces and mathematical statements are retained.
-/

module

public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.Valuation.DiscreteValuationField.Extensions
public import Mathlib
public import Mathlib.RingTheory.RamificationInertia.Basic

@[expose] public section
set_option backward.privateInPublic true


set_option autoImplicit false

/-!
# Defectlessness from a finite extension of valuation rings

The local Dedekind fundamental identity only needs discretely valued fields.
Completeness and Henselianity play no role once the target valuation ring is a
finite module over the base valuation ring.
-/

noncomputable section

namespace ValuationTheory.DiscreteValuationField.ValuedExtension

universe u v w x

variable {K : Type u} {L : Type w} [Field K] [Field L] [Algebra K L]

                                                                         
                                                                
                                    
                                                 
                                                  
                                                                 
                                                                     
                                  
           
                                                                     
                                        
                                                       
                 
                                                                              
                                                                                            
                
                                               
                                                              
                                                                              
                                 
                  
                                       
              
                                                                                       
                                                                   
                                                            
                                               
                                                                   
                                                   
                                                      
                 

end ValuationTheory.DiscreteValuationField.ValuedExtension

end
