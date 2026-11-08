/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Parabolic.Basic
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
public import Mathlib.Topology.Algebra.MvPolynomial

/-!
# Parabolically weighted polynomials on `ℝ × ℝ³`

Polynomials in the four coordinates `(z₀, z₁, z₂, z₃)` of `ParabolicSpace`, graded by the parabolic
weights `𝔰 = (2, 1, 1, 1)`. A weighted homogeneous polynomial of degree `n` scales like `c ^ n`
under `parabolicDilate c`, and a monomial of degree `n` is bounded by `‖z‖_𝔰 ^ n`.
-/

@[expose] public noncomputable section

namespace RegularityStructures

/-- The parabolic weights `𝔰 = (2, 1, 1, 1)`. -/
def parabolicWeight : Fin 4 → ℕ := ![2, 1, 1, 1]

/-- The four coordinates `(z₀, z₁, z₂, z₃)` of a point of parabolic space. -/
def parabolicCoords (z : ParabolicSpace) : Fin 4 → ℝ := ![z.1, z.2 0, z.2 1, z.2 2]

/-- Evaluation of a polynomial in four variables at a point of parabolic space. -/
def evalParabolic (p : MvPolynomial (Fin 4) ℝ) (z : ParabolicSpace) : ℝ :=
  MvPolynomial.eval (parabolicCoords z) p

end RegularityStructures

end

public section

namespace RegularityStructures

theorem weight_parabolicWeight (k : Fin 4 →₀ ℕ) :
    Finsupp.weight parabolicWeight k = 2 * k 0 + k 1 + k 2 + k 3 := by
  simp [Finsupp.weight_apply, Finsupp.sum_fintype, Fin.sum_univ_four, parabolicWeight]
  ring

                                                                      
                                                                                                      
          
                                                                              

                                                                          
                                                                                                
                                                                           
                      
                                                                                  
                   
                                            
                                                                                          
                                                                   
                                                  
                                                           
                                                                                    
                     
          
                                                                                    
                                                              
                                            
                   
      

                                                               
                                      
                      
                                                 
                        
                                  
                                   

                                                                             
                                                                                                       
                      
                                                                              
                                                  
                                   
                                             
                                                  
                          
                                                                          
              
                                                                          
                        
                                                         
                        
                                    
                                                                                                
                                     
                             
                                                                        
                                                          
                                                                                   
                                   
                  
                       
        
        
              
              
              

end RegularityStructures

end
