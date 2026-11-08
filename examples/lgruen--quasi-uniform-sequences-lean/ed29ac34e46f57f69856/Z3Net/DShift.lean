/-
Paper: L. Gruenschloss, "Low-discrepancy quasi-uniform digital nets in every dimension"
(the nets paper (hexagon:2610.00217v1); development revision).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Z3Net.DShiftDefs
public import Z3Net.FNie
public import Z3Net.FFrame
public import Mathlib
@[expose] public section

/-!
# V14 stage S10′: digital shifts (`def:dshift`, `lem:shift`)

* Digits of an integer coordinate at scale `q^m` (`digSum_digit`, `digSum_recon`); the shift of one
  coordinate (`dshiftCoord`): its digits, the prefix of its leading `d` digits is the shift of the
  prefix (`dshiftCoord_prefix`), and it is a bijection of `[0, q^d)` (`dshiftCoord_neg`).
* `digPointShift` is `dshiftPt` of `digPoint` (`digPointShift_eq_dshiftPt`); `τ = 0` gives `digPoint`.
* A digital shift maps every elementary box of shape `d` bijectively onto one of the same shape, so it
  preserves the exactness of every box shape (`dshift_boxExact`) and the `(0,m,s)`-property
  (`dshift_net`, `digPointShift_net`) of any point set.
* `lem:shift` for graph forms with any depths `K` (`shift_graph`): after re-indexing `n = v + T`, the
  shifted net is the affine graph form with offsets `Φ n + γ`, `γ_c = τ^off_c − ∑_d Φ_cd τ^cell_d`; one
  point in every cell (`shift_graph_cells`).
-/

namespace Z3NetF.Proofs

open Finset Matrix

noncomputable section

/-! ## Digits of an integer coordinate -/

section digits

variable {q : ℕ}

                                             
                                                                               

                                
lemma digSum_digit (hq : 0 < q) (m : ℕ) (f : Fin m → ℕ) (hf : ∀ j, f j < q) (j : Fin m) :
    Z3Net.Proofs.digSum q m f / q ^ (m - 1 - (j : ℕ)) % q = f j := by
  have hj := j.isLt
  have h1 := digSum_div_prefix q hq m f hf ((j : ℕ) + 1) (by omega)
  rw [show m - ((j : ℕ) + 1) = m - 1 - (j : ℕ) by omega] at h1
  rw [h1, Z3Net.Proofs.digSum_succ, Nat.mul_add_mod, Nat.mod_eq_of_lt (hf _)]
  rfl

                                                           
                                                          
                                                                              
         
                  
                                                                              
                
              
                                 
                                  
                                                                  
                                                                                                
                                                                  
              
                       
                                              
                                  
                    
                          
                                                                                     
                             

variable [NeZero q]

                  
                                                           
                                                 
                                                                                    

                                                                                          
                                                       

                                          
                                                                          
                                                     
                                                                        
                     
                                                                         

                                                               
                                                                             
                                                        
                     
                                                              
         
          
                                                                                                     
                

                                                                                              
                                                                                    
                                       
                                                                                        
                                                                                                  
                   
         
          
                   
           
                                                                                                   

end digits

/-! ## Digital point sets -/

section digital

variable {q : ℕ} [NeZero q] {s m : ℕ}

                                                    
                                                                                          
                                                                          
                                                                                             

                                                                                            
                                                                               
                                                       
                                                                                          
          
                                                                                        
                                    
                                                       

                  
                                  
                                                                          
                                                              
            
                                                            

                                                                                                  
                                                                           
                                                         
                                    
                                                                        
          
                                  
                                                                                         
        

                                                                    
                                                                   
                                               
                                                       

                                                                                                  
                                        
                                                       

end digital

/-! ## Boxes and nets -/

section boxes

variable {q : ℕ} [NeZero q] {s m : ℕ}

                                                                        
                                                                          
                                                                                                 

                                                                                           
                                                                                      
                                                                                          
                                                            
            
                                                                                               
                                              
                                                                    
                                                                 
                                                                    
                                                           
                                                              
                                                         
             
                                                                                                                            
                
                                                 
                                                                                
                                         
             
               
             
                                                                      
                                                        
             
            
                                                          
                           
                                   
                                                          
                               
                                   

                                                                                                      
                                                                                 
                                                              
                                                                    
            
                                        
                                                                                 
                                             

                                                                                     
                                                                       
                                                                                    
                                                            
                                                                
                                                     

end boxes

/-! ## `lem:shift` for graph forms -/

section graph

variable {q : ℕ} [NeZero q] {s m : ℕ}

                                                                                                
                                                                                              
                                                      
                                                                                          
        

                  
                                                                                             
                                 
                                                                                
                                   
              
                                                    
                                                                                                         
                
                         
               

                  
                                         
                                                           
                                                                     
                                                                                                     
                                                                         
                                                                             
          
                                          
                             
                               
                                                              
                                                                                                 
                                         
        
                               
                                                                                  
                                                                                                
          
           
                                                               
                                

                                                                                                        
                                                                                                           
                                                       
                                                                     
                                                                                         
                                               
                                                                                                 
                                                       
                                                                                                    
                                  
                                               
         
          
                                        

                                                                       
                                                     
                                                                       
                                                                  
                                                                                                                 
         

                                                                                          
                                                             
                                                                                                    
                                                                         
                                                                                     
                                                     

end graph

end

end Z3NetF.Proofs
