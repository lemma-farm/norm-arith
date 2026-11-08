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

public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.DiscreteValuationField.ValuationSubringUnits.CompleteRangeRestriction
public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.DiscreteValuationField.ValueGroup
public import Mathlib
@[expose] public section
set_option backward.privateInPublic true


set_option autoImplicit false

/-!
# Integer valuations from complete-DVF uniformizers

A chosen uniformizer determines the exponent of every nonzero field value and
therefore an integer-valued multiplicative valuation on field units.
-/

noncomputable section

universe u v

open WithZero
open scoped NNReal Valued WithZero

namespace LocalFieldTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField

namespace CompleteDVF

variable {K : Type u} [Field K]

                                                                              
         
                                    
                                                          
                                 
                                                            

                                                                                  
       
                                                           
                                                                                                 
     
                           

   
                                                                                                  
                                                                                  
  
       
                              
                                           
                                                                                        
                                                                                                                                                                       
     
                           

                                                                              
         
                                      
                              
                                                                       
                    
                                                

                                                                               
               
                                                              
                              
                                                                     
              
            
                                                                                                                                                                              
              
                                                                                    
                                    
                                                       
         
                                      
                                               
                                                                                                               
                                  
                                                  
                                                               
                                                                  
                                          

                                                                          
                                     
                              
                                                                     
               
                                                                                         
                                                                                             
                 
             
           
                 
                                 
                                       
                                                                    
                                                                
         
                                                                    
           
          

                                                                              
               
                                          
                              
                                                                     
                   
                  
                                                                                                                         

                                                                       
                                                                                
                              
                                                                     
              
                                                                                     
                                                                                               
                                                                                     
                       
                                                                                                                         

                                                                            
                                                                           
                                                        
                                                             
                              
                                                                       
                                           
                                                                                                
               
                                                                                                      
                                                                                                                                         
        
                   
                                                                                                      
        
                                                                                       
                                                                                                       
                                                                                                  
                                                                                                                                             
                                                                                                                                                                           
                                                                                           
         
                                                                                                                                                                                   
                                                                                                                                                                                         
                                                                                                                                             
                                                                                                                                           
         
                                                                                           
                                                                                                    
                                                                                                          
                       

   
                                                                                                  
                                               
  
       
                                                       
                              
                                                                     
              
                                                                                                                    
                                                                                              
     

                                                                               
                                                                 
                              
                                                                       
                                                                                                                          
                                          
                                                                                                                               
                                                                                                    
                                                                                                                                       
     
                                                 

                                                                             
                                
                                                                             
                              
                                                                       
                                                                                                                           
                                                  
       
                                                                                                  
                                       
                                                                                                    
                           
             
            
                  
                                                                                                                                           
                                
                   
                                                                   
                                                 
            
                                                                                                      
                                                                                                                                         
       
                                 

end CompleteDVF
end LocalFieldTheory.DiscreteValuationField

end
