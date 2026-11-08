module

public import SquaresInCircles.Common.Contacts
                                                  

/-!
# Supports of a square in a disk

Cauchy–Schwarz (`cauchy_sq`) bounds a linear form on the disk `X² + Y² ≤ Q`
(`dot_ge`, `dot_gt`, `dot_le_radius`). Some vertex of a square lies `width S n`
beyond its centre along `n`, so a square in the closed disk of radius `R` about
the origin has `⟨n, c⟩ ≤ R |n| - width S n` (`center_le_vertexSupport`); in the
frame of the square, with the far corner `(|a| + 1/2, |b| + 1/2)` in the disk,
the force `(U, V)` does work at most `R |(U, V)| - (|U| + |V|)/2` on the centre
`(a, b)` (`box_vertex_support`). The support function `support a b z` of the
closed axis-parallel square at `(a, b)` bounds the projection of each of its
points (`point_le_support`), and is at least `1/2 - ρ` when the centre is within
`ρ` of the origin (`support_ge`).
-/

@[expose] public section

noncomputable section
namespace SquaresInCircles

/-! ### Cauchy–Schwarz on a disk -/

/-- Cauchy–Schwarz on the disk `X² + Y² ≤ Q`. -/
lemma dot_sq_le {X Y p r Q : ℝ} (h : X^2+Y^2 ≤ Q) : (p*X+r*Y)^2 ≤ Q*(p^2+r^2) :=
  (cauchy_sq (p,r) (X,Y)).trans
    ((mul_le_mul_of_nonneg_left h (normSq_nonneg (p,r))).trans_eq (mul_comm _ _))

                                                                                 
                                                 
                                                             
                                               
                                                      

                                                             
                                               
                                                         

                              
                                                        

                                                                                

                                                                                               

                                                                     
                    
                                                                              
                                    
                                                                           
                              
                    

                         

                                                  
                                                             
                            

                                                                              
                                                          
                                                                  
                                                                          
                                                                          
                                                                                                 
                                                             
                            

                                                                  
                                              
                                                        
                                                                                    
                                              
                                               
                                                                                  
                       
          

                                                                      
                                                                                
                                                                    
                                                                                        
                                                                 
                                                                            
                                                  
                                                                     
                                                                     
          

                                                          

                                                                           
                                                         
                              
                                                         

                                                                                    
                                                   
                                                  
                                                                                               
                                                  
                                                                                               
                
          

                                                                                
                      
                                                                       
                               
                                                            
                                            
                                         
                
          

end SquaresInCircles
