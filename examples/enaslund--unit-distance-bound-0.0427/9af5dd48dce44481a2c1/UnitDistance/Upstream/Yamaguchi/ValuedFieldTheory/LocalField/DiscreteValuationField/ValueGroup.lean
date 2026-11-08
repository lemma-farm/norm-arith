/-
Ported from Naganori Yamaguchi, SawinTotallyRealTowers, commit
3a455e1aa9140dbbe7b7d68f508392a69c86d0f4, under Apache-2.0.
Modified: project-local imports relocated; Lean 4.32 compatibility changes
are recorded in third-party/yamaguchi/compatibility.patch.
Original declaration namespaces and mathematical statements are retained.
-/

module

public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.DiscreteValuationField.Norm.Quotients
public import Mathlib

@[expose] public section
set_option backward.privateInPublic true


set_option autoImplicit false

namespace LocalFieldTheory

/-!
# Integer value-group images

This file contains the integer value-group subgroup-image lemmas used by the norm and ramification-image arguments.  The results are purely about
integer-valued multiplicative valuations and integer lcm divisibility.
-/

noncomputable section

namespace DiscreteValuationField

                                                                      
                                                 
                                                 
                                                 
           
                                      
                                          
                                        

                                                      
                                             
                               
                              
                                                

                                                                              
                                              
                                                      
                                                 
                                                                 
       
                                                          
                                                                 
                                      
                                    
                                    
                                                                

                                                                              
                                                               
                                                      
                                                                       
             
           
                                                                      
                                                
                    
           
                                             

                                                                              
                                                       
               
                                                                
                                                                  
                                 
                                        
                                                              
                
                                                      
                                                                        

namespace MultiplicativeIntegerValuation

variable {G : Type _} [Group G]

                                                                              
                
                         
                                                             
                                     
                                                        
                                                    
                
                                        
                                                              
                
                         
                                                       

   
                                                                                           
                      
  
                                             
                                                           
                            
                                   
                                              
         

                                                                               
                                                                       
                                           
                                                                     
                                                        
                                        
                                                                 
             
                       
                                   
                                                     
                       
                                                    

                                                                              
                                  
                                                             
                   
                                                               
            
                                                
                                          
                              
                         

                                                                            
                                                                                
                                                            
                                                                     
                                                           
                                        
             
                
                                                                     
                                          
                        
                                
                                                      
                                                                                                      
                      
                
                                                  
                               
                                        
                                                                                                      
                  

                                                                               
                                    
                                                              
                                                                     
                 
                                                                  
                                                            
                                                

                                                                
                                                                                 
                                                                          
                                                                   
                                         
                                                               
                                
            
                                            
                        
                                      
                                      
                                      
                                                           
                                    

                                                         
                                                                 
                                                                       
                                       
                                                                
                                                                  
                              
                                                 
             
                                                                               
         
             
                                                                               
         

                                                    
                                                                       
                                                                         
                                       
                 
                                                                
                                                                  
                              
                                                                
                                                                     
                                                                     

end MultiplicativeIntegerValuation

end DiscreteValuationField

end

end LocalFieldTheory
