/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/

module
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.LinearAlgebra.Matrix.PosDef
@[expose] public section

/-!
# Completely positive matrices

A real matrix is completely positive if it is a finite sum of rank-one
matrices `vecMulVec p p` with entrywise nonnegative `p`.
-/

open Matrix

namespace BN

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A real matrix is completely positive if it is a sum of outer products of
entrywise nonnegative vectors. -/
def IsCompletelyPositive (C : Matrix n n ℝ) : Prop :=
  ∃ (q : ℕ) (p : Fin q → n → ℝ),
    (∀ a i, 0 ≤ p a i) ∧ C = ∑ a, vecMulVec (p a) (p a)

                                   
                                                               
                                           
                                         

                                   
                                                                       
                                                                      
                              
                                      
             
                                                  
                                                                     
                            

                                   
                                                   
                                                                 
                                      
                              
                                 
                                            
             
                                       
                             
                               
                         
        

                                   
                                                                                 
                                                     
         
                                                                                 

                                   
                                                                        
                            
                                                                               
             
                          
                                                         
                                       
          
                          
                                                                        

                       
                                                                           
                                  
                               
                                             
                                                         
                                                                                    
                                         

                       
                                                                                        
                      
                             
                                                                  

                       
                                                                                         
                    
                           

                       
                                                                                    
               
                                          

                                   
                                                                                  
                               
                              
                                               
                                                                

                                   
                                                                               
                                               
                                                
                                                                              
                                                        
                                                   
         
                                                    

end BN
