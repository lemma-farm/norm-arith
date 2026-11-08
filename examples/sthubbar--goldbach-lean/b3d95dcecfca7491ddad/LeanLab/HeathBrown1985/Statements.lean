module

public import Mathlib
                                     
                                             

/-!
P0096 D. R. Heath-Brown, The Ternary Goldbach Problem, Rev. Mat. Iberoam. 1 1985 45-59,
DOI 10.4171/RMI/2, read from the EMS scan 2026-10-16, pages 45 to 52.
STATED: the Siegel-Walfisz input 1.1, Theorem 1, Corollaries 1 to 3, Theorem 2, the function
Λ_Q, the bound 2.5, Lemma 1 as 2.6 and 2.7, Lemma 2 as 2.11. The paper's results are
classical and ineffective; here every analytic result is a `Prop`, with no open proof.
"≪" with constants depending on A, B, C is read as: for each such parameter some K, for
every x ≥ 2. L = log x throughout.
PROVED elsewhere in this folder: Corollary 1 from Theorem 1, Bridge.lean; Λ_Q in Ramanujan
sum form, Bridge.lean.
AI-written Lean code, Claude, run 20261016T2204Z-20593. Checked only by the Lean kernel.
Ternary Goldbach is a theorem, Helfgott 2013; binary Goldbach is OPEN.
-/

@[expose] public section

noncomputable section
namespace LeanLab.HeathBrown1985

open Real Finset
open scoped ArithmeticFunction.vonMangoldt ArithmeticFunction.Moebius

attribute [local instance] Classical.propDecidable

/-- `ψ(x; k, l) = Σ_{n ≤ x, n ≡ l mod k} Λ(n)`. -/
def psi (x : ℝ) (k l : ℕ) : ℝ :=
  ∑ n ∈ (Icc 1 ⌊x⌋₊).filter (fun n => n % k = l % k), Λ n

                                                                                    
                                                                                   
                                    
                           
                                                                                
                                                
                                                                                            

                                                                      
                             
                                                                                
                                     

                                                                                              
           
                           
                                         
                                                                        
        

                                                                                        
                      
                                            
                                                                                                 
                                     

                                                                                  
                               
                                                                            

                                                                                            
                                                                                        
                        
                                                                                           

                                                                                               
                                                                     

                                                                                      
                                                        
                        
                                                                                        

                                                                      
                                                                                             
                      
                                            
                                                                                            
                                                                                      

                                                             
                                  
                                                           
                                                 

                                                                
                                                                                  
                                                                                  

                                
                                                   

                                     
                                              
                                                         

                                                                
                      
                                            
                                                              

                                                                                          
                                                  
                      
                                                                                     
                     
                                                           
                                                                                   

                                                                                               
                                             
                      
                                                                                        
                 
                                
                                                                                
                                                        

                                                                 
                                                                                 

                                                                                                        
                    
                                                                              
                                                       
                                                                

                                           

                                                               
                            
                               
                     
                     
                         
                         

end LeanLab.HeathBrown1985
