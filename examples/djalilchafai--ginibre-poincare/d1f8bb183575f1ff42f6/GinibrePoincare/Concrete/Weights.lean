module

public import GinibrePoincare.Concrete.Vandermonde
public import Mathlib
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.NNReal.Defs
public import Mathlib.Tactic.Positivity

@[expose] public section

/-!
# Gaussian and Ginibre weights

This file defines the Euclidean square norm, the Gaussian weight, the
Vandermonde square, and the unnormalised Ginibre density.  The zero set of the
latter is proved to be exactly the collision locus.
-/

open scoped BigOperators NNReal

namespace GinibrePoincare

noncomputable section

/-- Euclidean squared norm on `ℂ^n`. -/
def configurationNormSq {n : ℕ} (z : Configuration n) : ℝ :=
  ∑ i : Fin n, Complex.normSq (z i)

/-- The Gaussian factor `exp (-n |z|²)`. -/
def gaussianWeight (n : ℕ) (z : Configuration n) : ℝ :=
  Real.exp (-(n : ℝ) * configurationNormSq z)

/-- The nonnegative squared modulus of the Vandermonde determinant. -/
def vandermondeWeight {n : ℕ} (z : Configuration n) : ℝ :=
  Complex.normSq (vandermonde z)

                                                                         
                                                      
                                          

                                                 
                                                                  
                                   
                            
                                                                

                                                
                                                          
                                
                       
                      

                                          
                                                             
                             
                                   

                                                      
                                                                
                                 
                               

                                          
                                                            
                               
                                              
                                

                                                        
                                                           
                                                 

                                                           
                                                              
                                                   

                                                       
                                                          
                                               

       
                                                            
                                                      
     

       
                                                               
                                                        
     

       
                                                           
                                                    
     

                                                               
                                                                     
                                                      
                                                
                                 

                                                            
                                                                 
                                                    
                      
                  
             
           
                               
                                                                   
                                                     
           
                                                          

                                                                         
                                           
                                                       
                                                                   
                            
                                                                          

                                                                   
                                      
                                                       
                                                             
                                                    

end

end GinibrePoincare
