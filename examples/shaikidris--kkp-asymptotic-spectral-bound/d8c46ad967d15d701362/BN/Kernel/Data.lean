/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/

module
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
@[expose] public section

/-!
# Three-column kernel data

Feature vectors, the Gram matrix `𝒜`, moment scalars, and the auxiliary
functions of `docs/sol.tex` §3 (`sec:kernel`, `eq:functions`). Coordinates of
`ℝ³` are numbered `0,1,2`.
-/

namespace BN

open Matrix
open scoped Matrix

noncomputable section

/-- Feature vector `v(t) = (1, -√2 t, t²)ᵀ`. -/
def v (t : ℝ) : Fin 3 → ℝ :=
  ![1, -Real.sqrt 2 * t, t ^ 2]

/-- Feature vector `b(x) = (x², √2 x, 1)ᵀ`. -/
def b (x : ℝ) : Fin 3 → ℝ :=
  ![x ^ 2, Real.sqrt 2 * x, 1]

/-- Truncated square `aᵢ(x) = (x - tᵢ)₊²`. -/
def truncSq (ti x : ℝ) : ℝ :=
  (max (x - ti) 0) ^ 2

                                             
                                                  
                                     
         
                                                       

                              
                                               
                                           
                         

                                                                                     
                                                          
                                                
                                                                                   

                                                         
                                                      
                                    
                                                                                         
                                                            
                                                              

                                                       
                                                                     
                                                          

variable {k : ℕ} (t : Fin k → ℝ) (q : Fin k → ℝ)

                                                 
                                   
                                              

                                                                            
                                                         
          
                                            
                                  
                                                                        

                                                 
                                                      
                          

/-- Moments `mⱼ = ∑ᵢ qᵢ tᵢʲ`. -/
def m (j : ℕ) : ℝ :=
  ∑ i, q i * t i ^ j

                                       
          

/-- Scalar `a₀ = 1 + m₀`. -/
def a0 : ℝ :=
  1 + m t q 0

                                          
             
                                              

                          
            
             

                         
                       
                        

                                        

                             
               
                                                                             
                                              
                       
                                                      

                                     
                          
      

                                              
              
                                  
                                                                              
                            
      
                                                          
                                        
                                                  
              
                                                             
                                                                            
                                                                            
                                                          
                                                
                                                             

                                                     
                                                    
                                                          
      
                                   
                                               
                                                  
              
                                                                    

                                                     
                                                    
                                                          
      
                                   
                                               
                                                  
              
                                                                    

                                                        
                         
                                                                    
                                                                              
                                               
                                               
              
                                                                                 
        
                                                         
                                                                      
                                                                    
                                              
                  
                                                                        

                                              
                                  

                                                   
                        
                                                                               

                                    

/-- `h(x) = ∑ᵢ qᵢ aᵢ(x)`. -/
def h (x : ℝ) : ℝ :=
  ∑ i, q i * truncSq (t i) x

/-- `h₁(x) = ∑ᵢ qᵢ tᵢ aᵢ(x)`. -/
def h1 (x : ℝ) : ℝ :=
  ∑ i, q i * t i * truncSq (t i) x

                                          
                               
                                              

                                   
                              
                                       

                                                    
                                              
                                                   

                                                            
                             
             
                                                   
                                                                                         

                                                            
                          
                                  

                           
                                           
                

                                
                    
                                     

/-- `P(x) = a₀ x + m₁ x² + m₁ h(x) − a₀ h₁(x)`. -/
def P (x : ℝ) : ℝ :=
  a0 t q * x + m t q 1 * x ^ 2 + m t q 1 * h t q x - a0 t q * h1 t q x

                                     
                      
                                    

                             

                                             
                                               
                                       
                             

end

end BN
