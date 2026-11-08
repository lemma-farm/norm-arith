/-
Ported from Naganori Yamaguchi, SawinTotallyRealTowers, commit
3a455e1aa9140dbbe7b7d68f508392a69c86d0f4, under Apache-2.0.
Modified: project-local imports relocated; Lean 4.32 compatibility changes
are recorded in third-party/yamaguchi/compatibility.patch.
Original declaration namespaces and mathematical statements are retained.
-/

module

public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.DiscreteValuationField.PrincipalUnits.AutomorphismTransport
public import Mathlib
@[expose] public section
set_option backward.privateInPublic true


set_option autoImplicit false

namespace LocalFieldTheory

open ValuationTheory
open ValuationTheory.DiscreteValuationField.ResidueField

/-!
# The first principal-unit quotient

Identifies valuation-ring units modulo first principal units with residue-field units and
records compatibility with valuation-preserving automorphisms.
-/

noncomputable section

open scoped BigOperators

universe u v

namespace DiscreteValuationField
namespace CompleteDVF

variable {K : Type u} [Field K]

namespace higherPrincipalUnitGroup

variable (F : ValuationTheory.DiscreteValuationField.CompleteDVF.{u, v} K)

                                                                      
                           
                               
                                                     
                                        
       
                                                                            

                                                                          
                                                          
                                                     
                                                                            
                         
                                  
       
                                                           
                                                          
                                           
                                                       
                                                           

   
                                                                                      
                                                                                                
   
  
                                                    
                               
                                                                
                                                              
                                                       
     

                                                                            
                          
                                                                                   
                 
           
              
                                          
                                             
                                                              
                                                                
                                                                       
                         
               
                                                                           
                                                                              
                                                 
                                    
                                                                        
                                                                  
                                                                  
                                                        
end higherPrincipalUnitGroup

end CompleteDVF
end DiscreteValuationField

end

end LocalFieldTheory
