/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/

module
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Order.Fin.Basic
public import Mathlib.Tactic.Ring
@[expose] public section

/-!
# Total nonnegativity

A real matrix is totally nonnegative when every square minor formed by
strictly increasing index maps is nonnegative. The empty (`k = 0`) minor is
the determinant of a `Matrix (Fin 0) (Fin 0)`, which Mathlib sets to `1`.

Cauchy–Binet is proved only for a product with middle dimension `3`, by
enumerating the `C(3, r)` strictly increasing maps `Fin r → Fin 3`
(`r = 0,1,2,3`) and using rank for `r > 3`.
-/

open Function Matrix

namespace BN

/-! ### TN01: definition -/

variable {m n : Type*} [LinearOrder m] [LinearOrder n]

                                                                       
                                                                     
                                                                           
       
                                                
                                            
                                                           

                                                             

                                                                             
                                                    
                                                
                                                               
                                    

                                                                       
           
                                                                       
                                     
                                            
                                                                                        

                                       
                                                    
                                                      
                                                                         
                       
                                                     
                                                              
                                                     
                                                          

                                                                            
                                                                             
                                                                          
                                                               
                                                                    
                                                                         
                              
                                
                                                                
                                                   
                                                                    
                                                                  

                                        

                                                                         
                                      
abbrev StrictMonoFin3 (r : ℕ) := {f : Fin r → Fin 3 // StrictMono f}

instance {r : ℕ} : DecidablePred fun f : Fin r → Fin 3 ↦ StrictMono f := by
  classical
  infer_instance

noncomputable instance {r : ℕ} : Fintype (StrictMonoFin3 r) :=
  Subtype.fintype _

                                                                   
                                      
              
                                                      
                            
                                    
       

                                                      
                                                                   
                         
                                  
                                
                                                
       

                                                               
                                 
                
                                                                                           

                                                                                     
       
                                           

                                                                                 
                                          
                           
                                                   
                                                                                  
                                               
                
                                                                          
                                                          
         
                       
                                                                 
                               
                                        
                
                                                             
                
                 
                                                                                
                                                       
           
               
                                                       
               
                               
                                                                               
                            
                                                                
     

                                                                            
                                           
                                                         
                                               

                                                                         
                                     
                                                                                    
                                                           
                                  

                                                                   
                 
                                                     
                                        

                                                                 
                                     
                                                                               
                                                   
                                                 

                                        
                                                          
                                       
                                                          
                                       
                                                          
                                      
                                                          
                                       
                                                          
                                      
                                                          

                                                                                
                                                       
                                    
                 
                                                                                       
                                                                                       
                                                                                           
                                                                                
                                                                               
                                                                            
      

                                                          
                                              
                                                                   
                 
                                                                                       
              
        
                                        
                                                           
                                                                  
                                                                              
        
                                                    
                                                          
                                                                          
        
                                                        
                                                          
                                                                                
        
                                              
                                                                                                  
                                                       
                  
            
                                   
                                                  
                                                          

variable {ι κ : Type*}

                                     
                                                     
                                     
                                                                         
         
                                                    

                                                                        
                                                                
                                                                    
                                                     
                                     
                                          
                              
                                          

                                                                         
                                                                         
                                                                        
                                                                       
        
                                                           
                                                     
                                     
                                  
                             
                                                               
                                                                
                                          
                                                                                  
                                                            

                                                    

                                                                            
                                                                           
                                                              
                                                                   
                                                     
                                                       
                                  
                   
                     
                                                       
                                                      
                                     
                                                        

end BN
