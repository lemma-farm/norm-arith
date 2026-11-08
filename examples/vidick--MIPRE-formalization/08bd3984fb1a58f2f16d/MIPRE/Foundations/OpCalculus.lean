/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import Mathlib.Analysis.CStarAlgebra.Basic
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.StarOrder
                           

@[expose] public section

/-!
# The state calculus on a Hilbert space

The estimates of the rigidity arguments are chains of bounds `‖T ψ‖ ≤ …` for operators `T` in
front of a fixed state `ψ`. This file is that calculus for bounded operators on any complex
inner product space:

* `Op.snorm ψ T = ‖T ψ‖`, with the triangle inequality, scalars, a bound in front and an
  isometry in front;
* `Op.Bnd T K`, the bound `‖T v‖ ≤ K ‖v‖` for every `v`, closed under sums, products and
  scalars;
* `Op.qform ψ T = Re ⟨ψ, T ψ⟩`, additive in `T`, with `‖T ψ‖² = qform ψ (T* T)`.

It is the first piece of the operator calculus of Phase 1(b) of `planning/mipco-track.md`,
which restates the matrix calculus over `H →L[ℂ] H` so that the stage analyses can be read in
any model with two commuting families of measurements. The matrix calculus of
`MIPRE/Foundations/OpBound.lean` is its instance on `EuclideanSpace ℂ N` through
`Matrix.toEuclideanCLM`, and its lemmas are proved from these.

As in the matrix calculus, the bound is a relation rather than the operator norm, and nothing
here uses the Loewner order on operators: the estimates need neither.
-/

namespace MIPRE

namespace Op

open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-! ## The bound -/

/-- `‖T v‖ ≤ K ‖v‖` for every `v`: the operator norm of `T` is at most `K`, as a relation. -/
def Bnd (T : H →L[ℂ] H) (K : ℝ) : Prop := ∀ v, ‖T v‖ ≤ K * ‖v‖

                                                                            
                                       
                                   
              
                                                            

                                                                            
                                       
                                   
              
                                                            

theorem Bnd.mul {T T' : H →L[ℂ] H} {K L : ℝ} (hK : 0 ≤ K) (h : Bnd T K) (h' : Bnd T' L) :
    Bnd (T * T') (K * L) := fun v => by
  show ‖T (T' v)‖ ≤ K * L * ‖v‖
  rw [mul_assoc]
  exact le_trans (h (T' v)) (mul_le_mul_of_nonneg_left (h' v) hK)

                                                         
                                                                                  
                                                                         

                                   

section SNorm

variable (ψ : H)

                                      
                                      

                                                                     

                                                                                      
                          

                                                                                      
                          

                                                                                  
                           

                                                                                 
                   

                                                                    

                                    
                                                                             
                                        
          

                                                 
                                                                     
                                                         
              
                       
                       

end SNorm

/-! ## The quadratic form -/

section QForm

variable (ψ : H)

                     
                                                

                                                                                      
                                 
                                      
     

                                                                                      
                                 
                                      
     

                                                                                             
                                    
                                              
     

                                                      
                              
                                        

                                                                  
                                                         
           
                                         
                                                                
                                                                                      

                                                                    
                        
                                                                 

                          
                                                              
                        
                                                    

                                                                    
                                                                              
                       
                                                                                 
              
                              

                                          
                                                                      
                                
                                                      
                      
          

end QForm

/-! ## Isometries and adjoints -/

section Adjoint

variable [CompleteSpace H] (ψ : H)

                                          
                                                                                            
                                                          
                                                              

                                                                                         
                                        

                                                      
                                                                                          
                           

                                                                                           
                                                                                        
         
                                                                           
                                         
                                      
                                                                        
                                        
                                                               
                                                
                                                                       
            
              
                                              

                                            
                                                                                     
                                    
                                 

                                                                                             
                                                                                             
                                             
                                                                              
                                                                                       
                                             
                                                   
              
                
                                                                        
                                             
                               
                                                                       
                                                                              
                                    

                                                                  
                                                                                      
                                             
                                                                                   
                                                  

end Adjoint

end Op

end MIPRE

end
