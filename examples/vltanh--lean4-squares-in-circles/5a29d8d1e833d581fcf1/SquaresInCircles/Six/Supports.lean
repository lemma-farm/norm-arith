module

public import SquaresInCircles.Six.Normalization.Basic

/-!
# Six squares: supports of the squares in the disk

A force `(U, V)` does work at most `R0 |(U, V)| - (|U| + |V|)/2` on the centre
`(a, b)` of a chart in the disk of radius `R0`, by its far vertex
(`local_vertex_support`), and the centre lies within `ρ0` of the origin
(`chart_radial_work`). A linear function on the part of the disk beyond a line
`A = l` is largest at a corner of that part (`disk_corner_support`,
`circle_support_above_primary`), so a force close to the primary axis has the
cap bound `ρ0 U` (`cap_linear_upper`); the far corner gives
`a + (31/100)(|b| + b²) ≤ ρ0` (`radial_transverse_quadratic`), and hence the
cone supports `ρ̄ U` for `|V| ≤ (31/100) U` and `ρ̄ U` plus a multiple of `V²`
in wider cones, by completed squares; and the force `(z + sin q, cos q - 1)` on
D has length at most `(2 + z²/4) sin (q/2) + z cos (q/2)` (`chord_support`). The
centre of C lies in the box `[0, c0]²`, where the work of a force is largest at
a corner or on the face chosen by the sign of a component (`center_face`).
-/

@[expose] public section

noncomputable section
namespace SquaresInCircles.Six
open Normalization

/-! ### The far vertex -/

                                                                    
                                                                            
                                                   
                                                                    

                                                                                
                       
                                                                             
                           
                                             
                                       
                                                                        
                                                    
          

                                                                          
                                      
                                                                     
                                                 
                                   
                                          
                                                                                               
                                                                      
                                      
                                    
                          

                                                                           
                                                                            

                                                                       
                                                           
                                                     
                                                                          
                                
                                       
                                                                       
                                                                          
                                                  
                                        
                                                                                             
                                                              
                                                                    
                                                   
                                                                    
                                                                          
                  
                         
                                                                                             
                                                                
                                                                        
                                                                 

                                

                                                                            
                                                                              
              
                                           
                                          
                                                              
                                                                  
                                               
                                                    
                                                  
                                                                   
                                                              
             
              
                            
                                                                       

                                                                           
                                    
                                                                
                                                       
                           
                                                            
                                                    
                                                                 
                                                               
                                                           
                                                                                            
           

                                                         
                                                                           
                                            
                                               
                                                             
                                                                                       
                           
                  

                                                 
                             
                                       
                                                                
                                                                        
                                                                         
                                        
                                                     
          

                                                                             
                                                                            
                       
                                                    
                             
                                     
                                           
                        
                                                      
                             
                                               
                                                   
                                   
                                                       
                                                                   
                                                     
                                                    
                                               
                                                  
                             
                             
                   
                                         
                                                         
                                           
                                     
                                                                   
                                            
                                                              
                                    
                                 

                                                                    
theorem radial_transverse_quadratic {a b : ℝ} (hc : ContainedChart a |b|) :
    a+(31/100)*(|b|+b^2)≤rho0 := by
  have ha := hc.a_le_rho0
  have hcircle : |b|+b^2≤(rho0-a)*(rho0+a+1) := by
    nlinarith [hc.containment,rho0_sq,sq_abs b]
  have hcoef : (31/100)*(rho0+a+1)≤1 := by
    linarith [rho0_bounds.2]
  have hprod := mul_nonneg (sub_nonneg.mpr ha)
    (show 0≤1-(31/100)*(rho0+a+1) by linarith)
  nlinarith only [hcircle,hprod]

                                                                             
                                                            
                                          
                              
                                             
                                                                                    
                                                         
                                                                              
                                                             
                              

                                                                               
                                                            
                                     
                                     
                                             
                                                
                                                    
                                                                                         
                                                                 
                                                                                 
                                                                      
                                                         
                           
                                                          
                            
                                                     

                                                               
                      
                                                            
                                           
                                         
                                             
                                                
                                                    
                                                                                         
                                                                                   
                                                                                 
                                                             
                                                         
                           
                                                          
                            
                                                     

/-- The support of a nearly radial force exceeds `ρ0 U` by at most `1/160`,
by the far-corner bound `a + (31/100)(|b| + b²) ≤ ρ0` and a completed square. -/
theorem narrow_support {a b U V : ℝ} (hc : ContainedChart a |b|)
    (hU : 3/5≤U ∧ U≤7/10) (hV : |V|≤(2/5)*U) : U*a+V*b≤rho0*U+1/160 := by
  have hU0 : 0≤U := by linarith [hU.1]
  have hrad := radial_transverse_quadratic hc
  have hm := mul_nonneg hU0 (show 0≤rho0-a-(31/100)*(|b|+b^2) by linarith)
  have hlinear := mul_nonneg (show 0≤(31/100)*U-(31/40)*|V| by linarith [hV]) (abs_nonneg b)
  have hquadratic := mul_nonneg (sub_nonneg.mpr hU.1) (sq_nonneg b)
  have hproduct : V*b≤|V| *|b| := by simpa only [abs_mul] using le_abs_self (V*b)
  have hsq : 0≤(31/100)*(3/5)*|b|^2-(9/40)*|b| *|V|+(7/100)*|V|^2 := by
    nlinarith [sq_nonneg (|V|-(45/28)*|b|),sq_nonneg |b|]
  rw [sq_abs,sq_abs] at hsq
  have hsoft : U*a+V*b≤rho0*U+(7/100)*V^2 := by
    nlinarith only [hm,hlinear,hquadratic,hproduct,hsq]
  have habs : |V|≤7/25 := by linarith [hV,hU.2]
  have hbound : V^2≤(7/25:ℝ)^2 := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr habs) (show 0≤7/25+|V| by positivity),sq_abs V]
  nlinarith only [hsoft,hbound]

/-! ### The box of the centre of C -/

                                                                                
                                                                                 
                     
                       
                                            
                                                
                                                               

                                                                         
                                                   
                                               
                                          
                                                   
                                   
                                                                      
                                                                      
                                                 
                                                 
                                             
                                             
           

                                                                             
                                                      
                                                                                             
                                     
                                 
                                                                                                   

                                                                                
                                                                                
             
                                                                    
                                    
                                                                    
                                             
                     
                                                                         
                                                                                             

end SquaresInCircles.Six
