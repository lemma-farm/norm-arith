/-
Generic finite L2 multiplication identities ported from F:/Lean2/SparseFockFormal/FiniteL2.lean.
Source SHA256: 3458808EFC640543597FB374D2A3998975E8933CD1B793D287449606C54BAD31
Only the outer namespace was changed; this is not a graph-specific estimate.
-/

import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

namespace GraphMatrices

namespace FiniteL2

open scoped BigOperators

variable (Omega I : Type*) [Fintype Omega] [Fintype I]

/-- A completely explicit orthonormal basis of a finite weighted real `L₂`
space.  `reconstruction` records completeness, not merely orthonormality. -/
structure WeightedONBasis where
  weight : Omega → ℝ
  weight_nonneg : ∀ x, 0 ≤ weight x
  sum_weight : ∑ x, weight x = 1
  basis : I → Omega → ℝ
  orthonormal_same : ∀ i,
    (∑ x, weight x * basis i x * basis i x) = 1
  orthonormal_ne : ∀ i j, i ≠ j →
    (∑ x, weight x * basis i x * basis j x) = 0
  reconstruction : ∀ (f : Omega → ℝ) (x : Omega),
    f x = ∑ i, (∑ y, weight y * basis i y * f y) * basis i x
  vacuum : I
  vacuum_eq_one : ∀ x, basis vacuum x = 1

variable {Omega I} [DecidableEq I]

namespace WeightedONBasis

variable (B : WeightedONBasis Omega I)

noncomputable def expect (f : Omega → ℝ) : ℝ :=
  ∑ x, B.weight x * f x

                                                      
                                     

                               
                                                        
                    
           
                                                       
                             
                                                         

                                                 
                                              
                                          

                                                    
                                   

                                                           
                                                       
                                                             
                                   
                      
                            
           
                            
           
      

                                                                       
                                                                
                                   
                      

                                                                              
                                                         
                                                   

                                                  
           
         
                                             

                                     
                                                              
           
         
                       
                   
      
                                                  
                                                 
                                                     
                                                      
                                      
                     
                
                                 
                                                                          
                
                                     
                                                               
                                                            
                   
                    
                                                               
                                                            
                   
                    
                

                                           
                                                    
           
                  
                                  
                
                                    
             

                                      
                                                  
                                              

                                               
                                                                         
                  
                        

section MatrixValued

variable {A : Type*} [Fintype A] [DecidableEq A]

                                                                            
                                                 
                                                          
                               
                
                                                              

                         
                                                         
           
             
                        
                        
                      
           
                                                       
                                                    

                                                      
                                       
                                              
           
             
                        
                        
                       
                                                                  
                   
                                                  
                                                     
                                                               
             
                                                         
                                                               
            
                       
                        
                            
           
      
                                                      
                                                     
                                                         
                                                          
                                      
                     
                
                                     
                                                                              
                
                                                      
                                                                   
                                                                    
                   
                    
                                                                   
                                                                    
                   
                    
                

                                                            
                                                                
           
                  
                                                   
                
                                          
             

                                                                 
                                                              
                                                      
                        
                                                                                
                      
                            
           
                     
      

end MatrixValued

end WeightedONBasis

end FiniteL2

end GraphMatrices
