/-
Paper: L. Gruenschloss, "Low-discrepancy quasi-uniform digital nets in every dimension"
(the nets paper (hexagon:2610.00217v1); development revision).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Z3Net.ThmADefs
public import Z3Net.DShiftDefs
public import Z3Net.Defs
public import Mathlib
@[expose] public section

/-!
# Definitions for `sec:dgs`: digitally shifted nets of Theorem A, and the notions of Dick, Goda and Suzuki

V14 stage S10′.

* `Z3NetA.AGen`: the generator matrices of the net `𝒫^{U*_s}_{k,q}` of `thm:A` (`Apoint` is the digital
  point set of `AGen`, `Z3NetA.Proofs.Apoint_eq_AGen`), so that its digital shifts are
  `digPointShift q (s k) (AGen s q k) τ` (`def:dshift`).
* Namespace `Z3NetDGS`: the definitions of [DGS2] = J. Dick, T. Goda, K. Suzuki, *Quasi-uniform
  digital nets and sequences II* (arXiv:2501.18226v2), transcribed for a base `b ≥ 2` (an integer),
  dimension `d`, point sets `P ⊂ [0,1)^d` given as `Finset (Fin d → ℝ)`.
-/

namespace Z3NetA

open Matrix Finset Z3NetF

                 
                                                                                                      
                                                                                                    
                                                        
                                                                                                      
                                        
                                                 
                                                                               
        

end Z3NetA

namespace Z3NetDGS

open Finset Matrix

/-! ## The definitions of Dick, Goda and Suzuki [DGS2] -/

section defs

variable {d : ℕ}

/-- [DGS2, §2.3] the toroidal distance of two coordinates `a, b ∈ [0,1)`: `min(|a - b|, 1 - |a - b|)`. -/
noncomputable def torCoord (a b : ℝ) : ℝ := min |a - b| (1 - |a - b|)

/-- [DGS2, §2.3] the toroidal Euclidean distance `‖x - y‖_{2,T} = (∑_j min(|x_j - y_j|, 1 - |x_j - y_j|)²)^{1/2}`. -/
noncomputable def torDist2 (x y : Fin d → ℝ) : ℝ := Real.sqrt (∑ j, torCoord (x j) (y j) ^ 2)

                                                                                                             
                     
                                                                               

                                                                                                
                                                                   

                                                                                                            
                                                             
                                                                                               
                                                                        

                                                                                        
                                                                                               
                                                                                                      

                                                        
                                                                                                  
                               

                                                                                                            
                                                          
                                                                                    

                                                                                                        
                                                                                                          
                                    
                                                           
                                                      
                                                                               
                                                           

                                                             
                                                                            
                                                               
                                                               
                                                            

                                                                                 
                                                                          

                                                             
                                                                                                                    
                                                                  
                                                                               
                                                         

                                                                                                    
                                                                                
                                                                    
                                                            
                                                             

                                                                                                   
                                                                                                      
                                                                       
                                                            
                                                                

                                                             
                                                                              

                                                                                   
                                                                                    

                                                                                               
                                                                                  
                                                                                
                                                
                                                                                     

                                                                                                  
                                                                                   
                                                
                                                                                        

                                                                                                             
                                                                                        

                                                                                                        
                                                                                                               
                                                                                                             
                                                                                  
                                                       
                                                                                             

                                                                                   
                                                                                
                                                        
                                                 

                                                                                 
                                                                                                  
                
                                    

                                                                          
                                                                                                             
                                

                                                                                                       
                       
                                                         
                                                       

                                                                                                            
              
                                                                               
                                                       

end defs

end Z3NetDGS
