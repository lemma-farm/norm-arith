module

public import Catalan.Cyclotomic.GroupRing

/-! Prime-power injectivity for units in a prime cyclotomic field. -/
/-!
# `Catalan.Cyclotomic.UnitPowers`

Part of the Catalan formalization.
-/

@[expose] public section

open NumberField
noncomputable section
namespace Catalan
variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

                                                                         
                                           
                               
                                   
                                             
                                                                   
                                                        
                   
                                        
                                                       
                                                
                   
                                           
                                                                          
           
                                          
                                                             
                         
                   
                                                                  
                         
                        

                                                                             
                                                  
               
                             
                                                             
                                                                


local instance unitPowersFintypeG : Fintype (G p K) := Fintype.ofFinite _

                                                      
                                                   
                                 
                                                      
           
                   
                                                                            
               
                      
                             
           
                                                       
                                            
     

end Catalan
