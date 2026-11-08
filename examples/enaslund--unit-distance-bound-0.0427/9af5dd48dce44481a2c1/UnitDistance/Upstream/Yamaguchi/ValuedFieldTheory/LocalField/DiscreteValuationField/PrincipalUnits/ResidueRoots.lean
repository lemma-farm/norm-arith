/-
Ported from Naganori Yamaguchi, SawinTotallyRealTowers, commit
3a455e1aa9140dbbe7b7d68f508392a69c86d0f4, under Apache-2.0.
Modified: project-local imports relocated; Lean 4.32 compatibility changes
are recorded in third-party/yamaguchi/compatibility.patch.
Original declaration namespaces and mathematical statements are retained.
-/

module

public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.DiscreteValuationField.PrincipalUnits.Filtration
public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.Valuation.HenselLemma
public import Mathlib
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.RingTheory.RootsOfUnity.Basic

@[expose] public section
set_option backward.privateInPublic true


set_option autoImplicit false

namespace LocalFieldTheory

open ValuationTheory
open ValuationTheory.DiscreteValuationField.ResidueField

/-!
# Residue roots of unity

Hensel lifting identifies the finite residue-field unit group with the lifted roots of
unity in the valuation ring.
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
