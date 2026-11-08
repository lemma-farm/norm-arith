module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.CovarianceBoundsTrace
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.NearFullCutoff
import Mathlib.Tactic

/-! # Native matrix contractions and ellipticity bounds for the Gaussian sign -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder

open Matrix
open scoped BigOperators MatrixOrder

                                                                                 
                                                                           
                                                                                
                                                              
                            
                            
           
                            
           
      

                                                                           
                                                            
                                                       
                                                                       

                                                                              
                                                                                      
                                                                                        
                                                                 
                                           
                                                                            
                                                          
           
                                                              
                                                                  
        
                                                                    
                                                               
                                                          
      

                                                                                 
theorem loewner_quadratic_lower {d : ℕ} {A : PDE.Mat d} {lam : ℝ}
    (hl : lam • (1 : PDE.Mat d) ≤ A) (p : PDE.Vec d) :
    lam * PDE.vecNormSq p ≤ PDE.vecDot p (A.mulVec p) := by
  have hp := (Matrix.le_iff.mp hl).dotProduct_mulVec_nonneg p
  simp only [star_trivial, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    dotProduct_sub, dotProduct_smul, smul_eq_mul] at hp
  change 0 ≤ PDE.vecDot p (A.mulVec p) - lam * PDE.vecNormSq p at hp
  linarith only [hp]

                                                                         
                                                             
                                                                    
                                               
                                                                  
                                                 
                    

                                                                                   
                                                                               
                                                          
                                                        

end HypoellipticAleksandrov.KineticAleksandrov.Holder
