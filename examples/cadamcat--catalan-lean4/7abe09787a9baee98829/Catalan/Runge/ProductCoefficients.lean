module

public import Catalan.Runge.BinomialSeries

/-!
# `Catalan.Runge.ProductCoefficients`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
open scoped BigOperators Classical
open NumberField
noncomputable section
namespace Catalan.Runge

                               
                                                                           
                                                                                         
                                                      
           
                          
                                               
              
                                
                                                                        
                     
            
                 
                       
              
                                                
                                    
          
                                                                                             
                     
                                                                        
                       
                                                         
              
       

                                                                                       
                        
                                
                                                             
          

section Cyclotomic
variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

local instance productCoefficientsGalFintype : Fintype (G p K) := Fintype.ofFinite _

                                                                                            
                                  
                                                                           
                                         
                                                                                               
                                                 
     

end Cyclotomic
end Catalan.Runge
