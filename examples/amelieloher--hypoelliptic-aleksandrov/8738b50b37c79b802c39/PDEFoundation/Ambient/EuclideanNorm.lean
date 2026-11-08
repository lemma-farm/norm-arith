module

public import PDEFoundation.Ambient.Basic
public import Mathlib
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Explicit Euclidean norm on native vectors

`PDE.Vec d = Fin d → ℝ` inherits the finite-product supremum norm. This
module supplies the distinct Euclidean dot product, squared norm, and norm
needed by energy estimates.
-/

@[expose] public section

open scoped BigOperators

namespace PDE

/-- The Euclidean dot product on native project vectors. -/
def vecDot {d : ℕ} (x y : Vec d) : ℝ :=
  ∑ i, x i * y i

/-- The square of the Euclidean norm on native project vectors. -/
def vecNormSq {d : ℕ} (x : Vec d) : ℝ :=
  vecDot x x

/-- The Euclidean norm on native project vectors. -/
noncomputable def vecEuclideanNorm {d : ℕ} (x : Vec d) : ℝ :=
  Real.sqrt (vecNormSq x)

                                           
                                 
               
                                
             
      

theorem vecNormSq_eq_sum_sq {d : ℕ} (x : Vec d) :
    vecNormSq x = ∑ i, x i ^ 2 := by
  simp [vecNormSq, vecDot, pow_two]

theorem vecNormSq_nonneg {d : ℕ} (x : Vec d) :
    0 ≤ vecNormSq x := by
  rw [vecNormSq_eq_sum_sq]
  exact Finset.sum_nonneg fun i _hi => sq_nonneg (x i)

theorem sq_apply_le_vecNormSq {d : ℕ} (x : Vec d) (i : Fin d) :
    x i ^ 2 ≤ vecNormSq x := by
  rw [vecNormSq_eq_sum_sq]
  exact Finset.single_le_sum
    (fun j _hj => sq_nonneg (x j))
    (Finset.mem_univ i)

                                                                    
                                                    
                                          
                                   
                                           

                                                                         
                                                  
                                                      
                             
                                     
                             
                                                 
                                               
                             
                                                 
                                  
                                    
          

                                                        
                                                  
                   
                                                       
                                
                                              
                        
                        

                                                                     
                                                         
                                     
                          
                               
                                     
                                                      
                                           
                                          
             
                                      
                                                      
                                               
            
                                
                                                           
             
                                          
                                                   
                                                   

theorem vecNormSq_eq_zero {d : ℕ} {x : Vec d}
    (h : vecNormSq x = 0) :
    x = 0 := by
  funext i
  have hi : x i ^ 2 ≤ 0 := by
    simpa [h] using sq_apply_le_vecNormSq x i
  exact sq_eq_zero_iff.mp (le_antisymm hi (sq_nonneg (x i)))

                                                   
                                 
             
                           
            
           
                            

theorem vecNormSq_smul {d : ℕ} (c : ℝ) (x : Vec d) :
    vecNormSq (c • x) = c ^ 2 * vecNormSq x := by
  rw [vecNormSq_eq_sum_sq, vecNormSq_eq_sum_sq]
  calc
    (∑ i, (c • x) i ^ 2) = ∑ i, c ^ 2 * x i ^ 2 := by
      refine Finset.sum_congr rfl ?_
      intro i _hi
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    _ = c ^ 2 * ∑ i, x i ^ 2 := by
      rw [Finset.mul_sum]

                                                    
                       
                                                      
                                             
                                                            
                                    
                                                       
                                                                       

                                                
                       
                                           
                                               
                        
      
                          
                                          
                                 
                 
                              
                                       
                                          
                         
                                               
                                 

                                                                
                                                         
                               
                                      
                                        
                                                         
         
        
        
      
                               
                                           
                   
                                                      
                                      
                                        
                                        
                                                            

                                                
                       
                                           
                                               
                        
      
                          
                                          
                                 
                 
                              
                                       
                                          
                         
                                               
                                 

                                         
                                                         
                   
                               
                                             
                         
      
                                                      
                      
                                                     
                                 
                 
                    
                                        
                                                   
                                                          
               
                                      
                                          
                                                                 

                                           
                                      
                                         
          

                                                  
                                               
                                   
         
                                          
        
                         

                                                     
                             
                    

theorem vecEuclideanNorm_sq {d : ℕ} (x : Vec d) :
    vecEuclideanNorm x ^ 2 = vecNormSq x := by
  exact Real.sq_sqrt (vecNormSq_nonneg x)

theorem vecEuclideanNorm_eq_zero_iff {d : ℕ} {x : Vec d} :
    vecEuclideanNorm x = 0 ↔ x = 0 := by
  constructor
  · intro h
    apply vecNormSq_eq_zero
    rw [← vecEuclideanNorm_sq, h]
    norm_num
  · intro hx
    rw [hx]
    simp [vecEuclideanNorm, vecNormSq, vecDot]

                                                      
                                        
                                       
                                 
                                                 

                                             
                             
                                    
                         
                                                    

                                                                 
                                                         
                                                 
                                             
                                                   
            
                                                  
                            
                             
                                        
                                                        
                                        
      
                        
                                  
         
                                               
                           
                             
                             

                                                  
                   
                                                                
      
                                                
                                  
                                                
                       
                                                  
                                                            
                                          
                                                      

theorem vecEuclideanNorm_smul {d : ℕ} (c : ℝ) (x : Vec d) :
    vecEuclideanNorm (c • x) = |c| * vecEuclideanNorm x := by
  rw [vecEuclideanNorm, vecEuclideanNorm, vecNormSq_smul]
  rw [Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]

                                                  
                                                    
                                                
          

                                                         
                                                             
                         
                         

                                                       
                              
                                                   
             
                                                             
                                                                  
            
                         
                                                           
             
                                               
                           
             
                                               
                           
                             
                            
      
                            
                                              
                 
                                                            
                           
                                                  
                  
                   
                                     
                                      

                                                      
                                  
                                                           
         
                                     
                                     

                                                              
                                         
                          
      
                                                        
                                 
                 
                                 
                                                          
                                                               
                               
                                           

                                                         
                 
                                                
      
                                                       
                                        
                                                            
                               
                                                                          

end PDE
