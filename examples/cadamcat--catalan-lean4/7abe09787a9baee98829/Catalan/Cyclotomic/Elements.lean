module

public import Catalan.Cyclotomic.Basic

/-!
# `Catalan.Cyclotomic.Elements`

Part of the Catalan formalization.
-/

@[expose] public section

open scoped BigOperators nonZeroDivisors Pointwise
open NumberField

noncomputable section
namespace Catalan

section Cyclotomic
variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

                                                          
                                                       
                                                                     
                                                             
                                                                             

                                                       
                                        
                                   
                         
                                      
         
                                          
                                                     
                                          
                                                                

                                                
                             
                                         
                                                                        
                                      

                                             
                             
             
                                                    
                                         
                                     
                                  
                       
                                   
                                                
                                                                
                              
              
                        
                                               

                                                                     
                                   
                                                      
                                             
                                                    
                                                            

end Cyclotomic
end Catalan
