/-
Copyright (c) 2026 Diar Heidary. Released under the MIT license.
-/
import SparseStackV3.SharedFactor
import Mathlib

/-!
# Concrete shared-factor insertion maps

The maps below insert the Parseval-frame vector `omega` into either of two
distinguished physical slots. Every other tensor register is collected in an
arbitrary finite spectator index `κ`. Thus the diagonal and cross-Gram identities
are derived from the frame, rather than supplied as norm assumptions.

The subsequent `ConcreteSharedFactor` modules prove the arbitrary-slot bound,
the normalized occupied-configuration compression, and the physical-site
exclusions. `Op.ConfigurationGram` and `Op.LightGramBound` identify this model
with the actual signed-hash operator and transfer its bound.
-/

open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator
open Matrix SparseFock ParsevalFrame

namespace SparseStackV3.ConcreteSharedFactor

noncomputable section

variable {n d : ℕ} {κ : Type*} [Fintype κ] [DecidableEq κ]

                                                           
                                           

                                
                                                           
                                                   

                                 
                                                           
                                
                                                       

                                                             
                                    
                                                                           
                                                           

                                            
                                               
                                

                                             
                                                      
                                                            
         
                    
           
                                                               
                                                     
                                                               
                                          

                                              
                                                        
                                                            
         
                     
                     
                                               
                                                                        
                                                   
                                     

                                                                                         
                                        

                                                                                            
                  
      
                                                 
                                                     
                                                                   
                                                               
                                                       
                                  
          

                                                                       
                                                         

                                    
                                                                             
         
                     
                     
                      
                                                                               
                                                                    
                                                   

                   
                                                 
                                                                
         
                                                                    
                           
                                                              
                                                        

                                                  
                                                                      
         
                     
                     
                                                                
                            
                      
                                                                               
                                                                      

                                                                                 
                                                                         
                                                                                  
                                                     
                                                                    
                           

                                            
                                                                 
                 
                                                                                            

                                                    
                                                                 
                                                                           
                                                                                
                                           
                                                       
                                                             
         
                            

                                   
                                                                  
                                   
                                                                 
                                                                       
        
                                                                                     
                               
                                             
                                                               
                               
                                                                 
                                                                 
                                              
                                                                                      
                                                          
                 
                           

                                   
                                                                          
                                                                             
                                                                 
                                   
                                                                      
                                     
                                      
                                     
                                                                   
                                      
      
                                                                               
                                      
                                                                           
                                       
                        
                                                                   
                                       
                      

end

end SparseStackV3.ConcreteSharedFactor
