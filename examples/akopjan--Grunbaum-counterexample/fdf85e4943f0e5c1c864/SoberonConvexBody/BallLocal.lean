import SoberonConvexBody.AffineBall
import SoberonConvexBody.ShellStability
import Mathlib
/-!
# Simultaneous low and high coefficient estimates near an orthogonal frame

The Jacobian is the determinant of the explicitly constructed coordinate map.
The low coefficients detect offsets and pairwise scalar products; the high
coefficients have no terms of degree zero or one.
-/
noncomputable section
namespace SoberonConvexBody.BallLocal
open Set MeasureTheory
open scoped BigOperators
open Tensors SphereGeometry NearIdentity Ellipsoid

                                                                              

                                                      
                                                         
      
                                                                       
                                                                            
                                       
                                                                          

theorem isometry_coordinateVector (q : Fin 4 -> E4) (hq : IsONFrame q) (j : Fin 4) :
    hq.toIsometry (coordinateVector j) = q j := by
  rw [IsONFrame.toIsometry_apply]
  fin_cases j <;> simp [coordinateVector_apply,linearCombination4]

theorem errorMatrix_normal (c : HyperplaneCfg) (q : Fin 4 -> E4) (hq : IsONFrame q)
    (e : E4 ≃ₗ[Real] E4) (he : forall x, e x = normalMap hq c.normal x)
    (i j : Fin 4) :
    errorMatrix e i j = inner Real (c.normal i) (q j) - if i=j then 1 else 0 := by
  simp [errorMatrix,he,normalMap_apply,isometry_coordinateVector,real_inner_comm]

theorem pair_gram_error (c : HyperplaneCfg) (q : Fin 4 -> E4) (hq : IsONFrame q)
    (e : E4 ≃ₗ[Real] E4) (he : forall x, e x = normalMap hq c.normal x)
    (d : Real) (hd : 0 ≤ d) (hn : forall i, norm (c.normal i-q i) ≤ d)
    (i j : Fin 4) (hij : i ≠ j) :
    |inner Real (c.normal i) (c.normal j)-(errorMatrix e i j+errorMatrix e j i)| ≤ d^2 := by
  have hid : inner Real (c.normal i) (c.normal j)-(errorMatrix e i j+errorMatrix e j i) =
      inner Real (c.normal i-q i) (c.normal j-q j) := by
    rw [errorMatrix_normal c q hq e he, errorMatrix_normal c q hq e he]
    simp only [if_neg hij,if_neg (Ne.symm hij),sub_zero,inner_sub_left,inner_sub_right,
      hq i j,if_neg hij,real_inner_comm (q i) (c.normal j)]
    ring
  rw [hid]
  calc
    |inner Real (c.normal i-q i) (c.normal j-q j)| ≤
        norm (c.normal i-q i)*norm (c.normal j-q j) := abs_real_inner_le_norm _ _
    _ ≤ d*d := mul_le_mul (hn i) (hn j) (norm_nonneg _) hd
    _ = d^2 := by ring

                                                                  
                                                                        

                                                           
                          
                                                                  
            

                                                                            
                               
                               
                                                        
                                                                                
                                     
                                                                                
                                      
                               
                                                                
                                                                              
                                                 
                                                                  
                                                        
                                           
                                                         
                          
                                       
                                                                      
                              
                                                                 
            
                                                 
                                                       
           
                                                    
                                  
                                    
                                                                      
                                                        
                                                
                                                                      
                                      
                                                         
                                                     
                                         
                                
                                                           
                                                    
                 
                                      
                     
                                         
                                                                       
                                 
                                   
                                                                                          
                                                     
                                           
                                                                                         
                                                 
                                                                       
                                                                                 
                                                                    
                                                             
                                                  
                                                                        
             
                               
           
                        
                                                                           
                                                                              
                                                                                     
                  
                                                                                   
                              
                                                              
                       
                 
                          
                                                                              
                                                                  
                                                               
                                                                                         
                                             
                                                                                     
                                                
                                                                           
                                                                       
                                                                                                        
               
                                                                  
                                              
                                         
                                                                              
                                 
                                                                                                 
            
                                
                            
                                                            
              
                      
                                                                                             
                  
                            
                                                            

                                 
                                         
                                                                     
                                                                                
                                                    
                                                     
                                                                                          
                                       
                                                                
                                                                                      
                                                           
             
                 
                                                                      
                                                                      
                                                                      
                                                                      
                                                                         
                    

end SoberonConvexBody.BallLocal
