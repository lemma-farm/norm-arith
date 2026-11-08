module

public import SquaresInCircles.Six.Supports

/-!
# Six squares: squares in a deep cap

A square in the closed disk of radius `R0` that lies beyond a line whose normal
makes the angle `t`, `|t| ≤ π/4`, with an axis of the square keeps the line
within `capDepth |t|` of the origin: with `A = |a| + 1/2` and `B = |b| + 1/2` on
the disk `A² + B² ≤ Q0`, the support `A cos t + B sin t` of the far corner along
the normal is at most its value at the corner `(ρ0 + 1/2, 1/2)` of the disk
below the angle `capSwitch = arcsin (1/(2 R0))`, and at most `R0` beyond it. A
cap at least `coreRadius` deep therefore forces `|t| < 2/5`, and one at least
`1/2` deep forces `|t| < 1/4`. In a cap `x ≥ h` with `h ≥ coreRadius` the square
has `|b| < a`, `h + 1/2 ≤ a ≤ ρ0`, `|b| ≤ U0` and `|b| < 1/2`
(`deep_cap_bounds`), and it contains the point `(h + 1/2, 0)` (`cap_piercing`):
otherwise its far vertex would leave the disk, by a polynomial positive on a
rectangle. A square with `a ≥ 0` and `|b| < 1/2` faces such a cap: its phase
lies within `2/5` of the normal modulo `2π` (`deep_cap_faces`), since a quarter
or a half turn would make the cap face a short or a negative coordinate.
-/

@[expose] public section

noncomputable section
namespace SquaresInCircles.Six.Normalization

/-! ### The cap depth -/

/-- The angle `arcsin (1/(2 R0))` at which the two branches of the cap depth
meet. -/
def capSwitch : ℝ := Real.arcsin (1 / (2 * R0))

/-- The cap branch: the far corner of the square at `(ρ0 + 1/2, 1/2)`. -/
def capFirst (t : ℝ) : ℝ :=
  (rho0 - 1 / 2) * Real.cos t - (1 / 2) * Real.sin t

/-- The vertex branch: the far vertex on the circle along the normal. -/
def capSecond (t : ℝ) : ℝ := R0 - Real.cos t - Real.sin t

/-- The depth of the deepest cap that holds a square at the angle `t`,
`0 ≤ t ≤ π/4`, to the cap normal. -/
def capDepth (t : ℝ) : ℝ :=
  if t ≤ capSwitch then capFirst t else capSecond t

private lemma switch_sine_bounds : 0 < 1 / (2 * R0) ∧ 1 / (2 * R0) < 1 := by
  have hp : 0 < 2 * R0 := by linarith [R0_pos]
  exact ⟨div_pos (by norm_num) hp,
    (div_lt_one hp).mpr (by linarith [R0_bounds.1])⟩

                                                 
                                                

private lemma sin_capSwitch : Real.sin capSwitch = 1 / (2 * R0) := by
  exact Real.sin_arcsin (by linarith [switch_sine_bounds.1]) switch_sine_bounds.2.le

                                                            
                                                
                                               
                                
                           
                                         
                          
          

                                                                     
                                                
                                            
                                
                           
               
                                                   
                                                                 
                                                                      
                          
                                                                  
           

private lemma cos_capSwitch : Real.cos capSwitch = (rho0 + 1 / 2) / R0 := by
  have hn : R0 ≠ 0 := ne_of_gt R0_pos
  have hid : 1 - (1 / (2 * R0)) ^ 2 = ((rho0 + 1 / 2) / R0) ^ 2 := by
    field_simp [hn]
    nlinarith [R0_sq, rho0_identity]
  rw [capSwitch, Real.cos_arcsin, hid, Real.sqrt_sq]
  exact div_nonneg (by linarith [rho0_bounds.1]) R0_pos.le

/-- Below the switch angle the corner `(ρ0 + 1/2, 1/2)` is the farthest point of
the disk along the normal: `(ρ0 + 1/2) sin t ≤ (cos t)/2`. -/
private lemma cap_low_branch_slope {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ capSwitch) :
    (rho0 + 1 / 2) * Real.sin t ≤ (1 / 2) * Real.cos t := by
  have hpi : capSwitch ≤ Real.pi / 2 := Real.arcsin_le_pi_div_two _
  have hs := Real.sin_le_sin_of_le_of_le_pi_div_two
    (show -(Real.pi / 2) ≤ t by linarith [Real.pi_pos]) hpi ht
  have hc := Real.cos_le_cos_of_nonneg_of_le_pi ht0
    (show capSwitch ≤ Real.pi by linarith [Real.pi_pos]) ht
  rw [sin_capSwitch] at hs
  rw [cos_capSwitch] at hc
  calc
    (rho0 + 1 / 2) * Real.sin t ≤ (rho0 + 1 / 2) * (1 / (2 * R0)) :=
      mul_le_mul_of_nonneg_left hs (by linarith [rho0_bounds.1])
    _ = (1 / 2) * ((rho0 + 1 / 2) / R0) := by
      field_simp [ne_of_gt R0_pos]
    _ ≤ (1 / 2) * Real.cos t := mul_le_mul_of_nonneg_left hc (by norm_num)

/-- A square with `h + (|cos t| + |sin t|)/2 ≤ a cos t - b sin t`, the support
inequality of a square in the cap `x ≥ h`, has `h ≤ capDepth |t|`, for
`|t| ≤ π/4`. -/
theorem cap_support_bound_signed {a b height t : ℝ}
    (ht : |t| ≤ Real.pi / 4)
    (hbox : (|a| + 1 / 2) ^ 2 + (|b| + 1 / 2) ^ 2 ≤ Q0)
    (hcap : height + (|Real.cos t| + |Real.sin t|) / 2 ≤
      a * Real.cos t - b * Real.sin t) :
    height ≤ capDepth |t| := by
  have htr := east_quadrant_trig (abs_nonneg t) ht
  have hcos : Real.cos |t| = |Real.cos t| := by
    rw [Real.cos_abs, abs_of_nonneg (Real.cos_nonneg_of_mem_Icc
      ⟨by linarith [(abs_le.mp ht).1, Real.pi_pos], by linarith [(abs_le.mp ht).2, Real.pi_pos]⟩)]
  have hsin : Real.sin |t| = |Real.sin t| :=
    (Real.abs_sin_eq_sin_abs_of_abs_le_pi (by linarith [Real.pi_pos])).symm
  have hA : a * Real.cos t ≤ |a| * Real.cos |t| := by
    rw [hcos, ← abs_mul]; exact le_abs_self _
  have hB : -(b * Real.sin t) ≤ |b| * Real.sin |t| := by
    rw [hsin, ← abs_mul]; exact neg_le_abs _
  have hab : height ≤ (|a| + 1 / 2) * Real.cos |t| + (|b| + 1 / 2) * Real.sin |t| -
      Real.cos |t| - Real.sin |t| := by
    rw [← hcos, ← hsin] at hcap
    linarith
  unfold capDepth
  split_ifs with hbranch
  · have hcorner := disk_corner_support
      (A := |a| + 1 / 2) (B := |b| + 1 / 2) (a := rho0 + 1 / 2) (b := (1 : ℝ) / 2)
      (c := Real.cos |t|) (s := Real.sin |t|)
      (by linarith [rho0_bounds.1]) (by linarith [abs_nonneg b]) (by linarith [htr.1])
      (by nlinarith [rho0_identity]) hbox (cap_low_branch_slope (abs_nonneg t) hbranch)
    dsimp [capFirst]
    linarith
  · have hround : (|a| + 1 / 2) * Real.cos |t| + (|b| + 1 / 2) * Real.sin |t| ≤ R0 := by
      nlinarith [sq_nonneg ((|a| + 1 / 2) * Real.sin |t| - (|b| + 1 / 2) * Real.cos |t|),
        Real.sin_sq_add_cos_sq |t|, R0_sq, R0_pos, abs_nonneg a, abs_nonneg b, htr.1, htr.2.1]
    dsimp [capSecond]
    linarith

/-! ### The angle of a square in a deep cap -/

                                                                                 
                                                                  
                                                              
                               
                                        

                                                       
                                                                             
                                                                         
                                     
                                                                      
                                         
                        
          

                                                                   
             
                                              
                                                           
                                              
               
                                                      

                                                    
                                                                        
                                                   
                                                                 
                                                       
                                                                     
                                                          
                                                       
                  
                           

                                                     
                                                                         
                                                                      
                                                                  
                                                              
                   
                         

                                                                          
                                           
                                                      
                                              
               
                         
                   
                                                     
                                                      

                                              

                                                                     
                                                                
                                                                         
                                      
                                                                            
                                                                     
                                 
                                                            
                                             
                                                                
                                                           
                                                 
                                                                             
                             

                                          
                                                
                                                        
                                                       
                                               
                                                    
                                   
                                                  
                                                                                        
                                             
                                               
                                                               
               
                                                   
                                                             

                                            
                                                      
                                                        
                                                       
                                               
                                                      
                                                     
                                   
                     
                                              
                               
                                                                     
                        
                                                           
                            
                
                                        
                                     
                         
                            
                                                
                                                   
                                                   
                                     
                                                         
                                 

                                            
                                                        
                                                       
                                               
                                                        
                                                            
                                   
                                                               
                                                         
               
                                           
                                    
                                                                
                            

                                                                    
                                                   
                                          
                                                                   
                          
                                                                          
                                                    
                                           
                                                            
                                                           
                       
                             
                                                
                                           
                                                       
                   
          

                                        
                                                    
                                                              
                                                       
                                               
                                                                                 
                              
                                                                                     
                                                                                                 
                                                                                        
                                                                                     
                                    
                                        
                                                                   
                                                  
                                                                 
                                                      
                                                                               
                                                       
                                                                          
                                       
                              
                                                                             
                                    
                                       
                                                               
                                            
                                              
                                                         
                                                             
                                             
                                                                       

                                                                               
                                                                      
                                                                                  
                                                     
                                                                                               

                                                                         
                                                                   
                                                                           
               
                                                                                    
                                                       
                                               
                                                                                   
                                    
                                  
                                                  
                                  
                                                                                   
                                        

                                                

                                                 
                                                                   
                     
                                               
                                     
                        
                                            
                                               
                                             
                                          
                                               
                                  
                                             
                                            
             
                                                                       
                                                                                
                                                                                
                                                                                   
             
                                         
            
                                               
                                                         
                                                                           
             
        
          

                                                      
                                      
                                    
                                                  
                                     
                                                                      
                                            
                                        
                    
           

                                                                              
                                                                         
                                                         
                                      
                                               
                        
                                                     
                                              
                                     
               
                                  
                                                                     
                                          
                                            
                                  
                                                    
                           
                                                                 
                                                    
                                                          
                                         
                                   
            
                                
                                                           
                                                 
                                                         

                                                                         
                                                                   
                                                  
                                                                                 
                                                       
                                               
                                                          
                                                       
                                                                                       
                                                         
                                      
                                                              
                                                                                         
                                          
                                                                                        
                             
                                      
                                                               
                                                                             
                
                          
                                                                                         
                                       
                                                           
                                                     
                                 
                                        
                                  
                                              
                                              
                                                                        
                                                                            
                                                                           
                                                                 
                                                                        
                                             
                                
                   
                                                   
            
             
                    
                                             
                    
                                        

                                    

                                                                
                                                                
                                                           
                                      
                                      
                                                             
                

                                                                    
                                                                                  
                                                                              
                                                                             
                                                                                          
                                                       
                                               
                                                                                         
                                        
                          
                                                                
                          
                                                                                            
                                              
                                                       
                                                         
                                                          
                                              
                                      
                                      
                                                                
                                                                                            
              
                                                                   
            
                                              
                                                  
                                                  
                                                             
                                                                
              
                                                                                  
            
                                              
                                                              
                                                                                         
                                                 
          
                                                              
                                                                                         
                                                 
          
                  
                  
                                                                
                                                                                            
              
                                                  
                                            
            

                                                                   
                                 
                                                                       
                                                      
                                                       
                                                                 
                                                          
                                          
                                                                              
                                                             

end SquaresInCircles.Six.Normalization
