-- Copyright (c) 2026 Scott Armstrong and Tuomo Kuusi.
-- Released under Apache 2.0 license.
-- From CoarseGraining (https://github.com/scottnarmstrong/CoarseGraining), commit c7ddd76.

module
public import Mathlib
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section

open scoped BigOperators

namespace Homogenization

abbrev Vec (d : ℕ) := Fin d → ℝ

abbrev Mat (d : ℕ) := Matrix (Fin d) (Fin d) ℝ

abbrev BlockVec (d : ℕ) := Vec d × Vec d

structure BlockMat (d : ℕ) where
  upperLeft : Mat d
  upperRight : Mat d
  lowerLeft : Mat d
  lowerRight : Mat d
deriving Inhabited

                                       
                

                                        
            

                                                                    
                                                    
                                          
                                                                         

                                                                    
                         
                             
            
                             

                                                               
                                     
                                         
                
                          
                              
                    
                 
                                    
                         
                                                     

                                                                        
                                                  
                                                       
                             
                                     
                              
                                                 
                                            
                          
                                                  
                                                                    
          

                                                                           
                                                                  
                                                       
                                
                                              
                                             

                                                                     
                                                         
                                     
                          
                                                             
                                                      
                                            
                                          
             
                                      
                                                      
                                                
            
                                
                                                           
             
                                          
                                                   
                                                   

                                                                                 
          
                                         
                                            
                           
                                       
                                
                                                   
                           
                           
                                    
                        
                              
                                 
                             

                                                                                 
             
                           
            
           
                            

                                                    
                                                 
                         
      
                                                               
                  
                    
          
                                    
          
                                                                           
                                 
         

                                                
                                                             
      
                                                  
                                       
                                          
                                 
                
                                       
                                          
          
                                                                     
                                               
                                 
                                             
                                                   
                                      
                  
                      
                                                   
                                      
                  
                      
                 
         

                                                                
                                                         
                               
                                                                       
                                                         
         
        
        
      
                             
                                                           
                                                      
                                        
                                                                         
                                                              

                                                
                                                             
      
                                                  
                                       
                                          
                                 
                
                                       
                                          
          
                                                                     
                                               
                                 
                                             
                                                   
                                      
                  
                      
                                                   
                                      
                  
                      
                 
         

def matVecMul {d : ℕ} (A : Mat d) (x : Vec d) : Vec d :=
  fun i => ∑ j, A i j * x j

def matTranspose {d : ℕ} (A : Mat d) : Mat d :=
  Matrix.transpose A

                                                 
                                 

def blockMatVecMul {d : ℕ} (A : BlockMat d) (X : BlockVec d) : BlockVec d :=
  ( matVecMul A.upperLeft X.1 + matVecMul A.upperRight X.2
  , matVecMul A.lowerLeft X.1 + matVecMul A.lowerRight X.2 )

@[simp] theorem blockMatVecMul_fst {d : ℕ} (A : BlockMat d) (p q : Vec d) :
    (blockMatVecMul A (p, q)).1 = matVecMul A.upperLeft p + matVecMul A.upperRight q :=
  rfl

@[simp] theorem blockMatVecMul_snd {d : ℕ} (A : BlockMat d) (p q : Vec d) :
    (blockMatVecMul A (p, q)).2 = matVecMul A.lowerLeft p + matVecMul A.lowerRight q :=
  rfl

noncomputable def symmPart {d : ℕ} (A : Mat d) : Mat d :=
  fun i j => (A i j + A j i) / 2

noncomputable def skewPart {d : ℕ} (A : Mat d) : Mat d :=
  fun i j => (A i j - A j i) / 2

                                                            
                                                         
         
                               
      

                                                            
                                                         
         
                               
      

@[simp] theorem matTranspose_symmPart {d : ℕ} (A : Mat d) :
    matTranspose (symmPart A) = symmPart A := by
  ext i j
  simp [symmPart, matTranspose, add_comm]

@[simp] theorem matTranspose_skewPart {d : ℕ} (A : Mat d) :
    matTranspose (skewPart A) = -skewPart A := by
  ext i j
  simp [skewPart, matTranspose]
  ring

end Homogenization
