module
public import Z3Net.FTs
public import Mathlib
@[expose] public section

/-!
# Entry F, part 6: the frame of `s` places with `m = s k`: graph form, `E`-basis, `prop:Ns`

* `frameGraph_spec_core`: the `(k, …, k)` box `G` of the frame is invertible and `Φ^F` (defined
  via Mathlib's `G⁻¹`) is the graph form of the frame.
* The `E`-basis: `E_{d,j} = Π_d (t - x_d)^j` (finite `d`), `E_{∞,j} = Π t^(k-1-j)`; its cells
  vanish off `d` and form `Toep(uN_d)` at `d`; its first offset digit at `c ≠ d` is
  `Q_c^k w_cd y_cd^(k-1-j)`. Hence `Φ^F_cd · Toep(uN_d) = Ψ_cd` (the offset digits of the
  `E`-basis), which gives `prop:Ns` (`Ns_row0_core`).
-/

namespace Z3NetF.Proofs

open Polynomial Finset Matrix

noncomputable section

variable {R : Type*} [CommRing R] {s m : ℕ}

/-! ## Graph forms: matrix-vector products -/

                                                                                                  
                                                                                              
                                                              
                                                           
      
                                                                
                                                                  
               
                              
                                                                     
                                               
             
                                                
                               
                

                                                              
                                                                                          
                         
                                                       
                                                                                                 
                                
                    
                                                                           
                                                               
         
           

                                                               
                                                                                          
                            
                                                                             
                                                   
                                
                                                                          
                                                                                  
                
                                                                            
                                   
        
                
                                           
                                                                            
                         
        

                                                                                               
                                                        
                                                                       
                                                                
                                                           
                                

                                                                                      
                                                                            
                                                   
                         

                         

                                                              

                                                                              
                                                            
                                                                            
                                  

                                

variable (k : ℕ) (inf : Fin s) (x : Fin s → R)

                                        
                                                   
                                                                

                                                                          
                                                 
                                                                                
                                      
                                       
                    
                                                      
                      
                                                                                       
               
                   

                            
                                                                                  
                                            
                
                                       
                                                            

                                                           
                             
                                                                                                    
                                              
                                          
                                                                                     
                                                                             

end

end Z3NetF.Proofs
