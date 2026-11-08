module

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/
public import Sidon.NumberTheory.RiemannGaussian.AnalyticDerivativeCutoff
public import Sidon.NumberTheory.RiemannGaussian.DerivativePowerExponents
public import Sidon.NumberTheory.RiemannGaussian.DerivativeRecursionBudget

@[expose] public section

namespace RiemannGaussian.DerivativePowerEnvelope
noncomputable section
open RiemannGaussian.DerivativePowerExponents RiemannGaussian.AnalyticDerivativeCutoff RiemannGaussian.DerivativeRecursionBudget
def mainTerm (k : ℕ) (L ℓ A : ℝ) : ℝ := A ^ amp k * L * ℓ ^ alpha k

def errorTerm (k : ℕ) (L ℓ : ℝ) : ℝ := L ^ beta k * ℓ ^ (-alpha k)

def envelope (k : ℕ) (L ℓ A : ℝ) : ℝ := 32 * (mainTerm k L ℓ A + errorTerm k L ℓ)

                                                                                
                                                          

                                                                  
                                                          

                                                                         
                                                                                  
                 
                                                                                         
                                                  
                                
                                     

                                                                  
                                                                  
                        
                                                                                 
                              

                                                                                   
                              
                                               
                                                 
                                                         
                                                    
                                           
                 
           

                                                                   
                                                           
                                 
                                 
                                                     
                                                                 
                                                
      
                                  
                                       
                                                                            

                                                                           
                              
                 
                                                                                             

                                                                              
                                             
                                                           
                                 
                                                        
                                                             
                             
                                                                              
                                                          
                                                
                                                                                              
                                    
                                                                              
                                             
                              

end
end RiemannGaussian.DerivativePowerEnvelope
