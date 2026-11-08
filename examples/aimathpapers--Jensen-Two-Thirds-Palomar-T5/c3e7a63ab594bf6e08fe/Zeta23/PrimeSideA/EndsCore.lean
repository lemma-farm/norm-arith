/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23 — prime side, [lem:ends] "End effects" (§5, §5.3 of the paper), with [eq:Kdef],
[eq:trG2int], [eq:Kbounds].

TARGET (consumed by thm:traces):
  theorem lem_ends (hΓ : GammaFacts) (hcheb : ChebyshevMertens) (hlam : 0 < lam ∧ lam ≤ 1) :
    ∃ C : ℝ, EventuallyAt cϱ lam (fun p F =>
      |trGt2A p F - MtotalA p F| ≤ C * (p.L * p.l * Real.log p.l * (p.l ^ 2 + p.X)))

PAPER (§5.3, verbatim): "For T ≥ T₀,  tr G̃² = 𝓜 + O(L l log l (l² + X)),
  𝓜 := ∬_{I×I} Φ(τ−τ')² ν_X(τ) ν_X(τ') dτ dτ'."

ROUTE (paper's, §5.3, with two simplifications that only change absolute constants):
* [eq:trG2int]  L² tr G̃² = Σ_{k,l<d} G_{kl}² = ∬_{ℝ²} K(τ,τ')² ν(τ)ν(τ') dτdτ',
  K(τ,τ') := Σ_{0≤k<d} φ̂(τ−τ_k)φ̂(τ'−τ_k) [eq:Kdef]  — here a product of two integrals and a
  FINITE sum, so no Fubini beyond ∫(f)·∫(g) = ∬ f⊗g.
* K_∞ := Σ_{k∈ℤ} φ̂(τ−τ_k)φ̂(τ'−τ_k) = L Φ(τ−τ') by [lem:poisson] (LocalHyps.poisson), so
  ∬_{I×I} K_∞² νν' = L² 𝓜, and  L²(tr G̃² − 𝓜)·L² … precisely:
  Σ G² − L²𝓜·… = 𝓔₁ + 𝓔₂,  𝓔₁ := ∬_{I×I}(K² − K_∞²)νν',  𝓔₂ := ∬_{ℝ²∖I×I} K²νν'.
* [eq:Kbounds]  |K|, |K_∞| ≤ L² (paper: aL²; a ≤ 1);  |K_out| = |K_∞ − K| handled by the
  weighted AM–GM  |Σ_{k∉[0,d)} a_k b_k| ≤ ½(s ρ(τ) + ρ(τ')/s), ρ(τ) := Σ_{k∉[0,d)} φ̂(τ−τ_k)²
  = aL² − Σ_{k<d} φ̂(τ−τ_k)² (Poisson diagonal — a FINITE expression), with s := g(τ')/g(τ),
  g := (1 + dist(·,∂I))⁻².  This replaces the paper's (∫_I ψ_k)²-sum (§5.3) and gives
  |𝓔₁| ≤ 2L²B²(∫_I ρ/g)(∫_I g) ≪ L²B²·L·l ≤ L³B² l log l  — within the lemma's error (the paper
  gets L³B² log L here; the slack l is free since 𝓔₂ is the dominant term anyway).
* 𝓔₂ exactly as the paper (§5.3): |𝓔₂| ≤ 2L² Σ_{k<d}(∫_{I^c}ψ_k|ν|)(∫_ℝ ψ_k|ν|),
  second factor ≤ 3Ψ₀B, Σ_k first factor = ∫_{I^c}|ν|σ ≪ BLl via the grid bound
  σ(τ) ≤ ψ(Δ) + h⁻¹∫_Δ^∞ψ, σ ≤ d ψ(Δ); for the far range we use log⁺x ≤ 2√x instead of
  integrating logarithms (constants only).
* [eq:Bdef] |ν_X(τ)| ≤ B + log⁺(|τ|/4T), B = l + 4√X: Zeta23/PiFacts.lean
  (from H-Γ + H-cheb); B² ≤ 2l² + 32X.
All constants C may depend on c_ϱ and λ (PrimeSideA convention); T₀ likewise.

FILE LAYOUT:
  EndsCore.lean (this file) — defs, continuity/integrability, [eq:trG2int],
     decomposition, ψ toolkit, [eq:Kbounds] pointwise;
  EndsE1.lean — calE1_bound;   EndsE2.lean (1-D estimates N1/N2 in EndsNu.lean,
     weights in EndsWeighted.lean) — calE2_bound;
  Ends.lean — assembly lem_ends' / lem_ends (proved from the two bounds).
-/
import Zeta23.PrimeSideA.Basic
import Zeta23.PiFacts

noncomputable section

open MeasureTheory Real Set Finset
open scoped BigOperators

namespace Zeta23
namespace PrimeSide

/-! The ψ majorant `psiA cϱ p r = min(L, 2/|r|, c_ϱ/(w r²))` [eq:psidef] and the [eq:psiints]
facts (psi_integrable, psi_sq_integrable, integral_psi_Ioi_le, integral_psi_sq_le, phiHat_le_psi,
Phi_le_psi) are in Zeta23/PrimeSideA (`LocalHyps`). -/

/-- [eq:Bdef] pointwise bound on ν_X (Zeta23/PiFacts.lean `nuX_abs_le`):
"`|ν_X(τ)| ≤ B + log⁺(|τ|/4T)` (τ ∈ ℝ), `|ν_X(τ)| ≤ B` (|τ| ≤ 4T), `B := l + 4√X`" for T ≥ T₀. -/
def NuBound (p : Setting) (B : ℝ) (ν : ℝ → ℝ) : Prop :=
  ∀ τ : ℝ, |ν τ| ≤ B + max (Real.log (|τ| / (4 * p.T))) 0

                                
                                                       

variable {cϱ : ℝ} (p : Setting) (F : LocalFun) (ν : ℝ → ℝ)

/-! ν-GENERIC LAYER (for Theorem E): every object below that involves the density is
stated for an ABSTRACT `ν : ℝ → ℝ` (hypotheses: `Continuous ν` and `NuBound p B ν` for a free
`B ≥ 0`); ζ is the instantiation `ν := Zeta23.nuX p.X`, `B := Bconst p` (bridges by `rfl`). -/

                                                                                                       
                                                                      
                                                            

                                                                                        
                                                                                

                                                                    
                                                              

                                                          
                                                      

                   

                                                             
                                                                                          

                                                                       
                                               

                                                                                                
                                                                                

                                                                                         
                                                                                         
                                          

                                        
                                   

                                                            
                                                                         

                                                                   
                                                                         

                                               
                                                                              

                                         
                                                       

variable {p F ν}

section Structure
variable {B : ℝ}
/-! ## [eq:trG2int] and the decomposition -/

                                                                                              
                                                                              
                                     
                                                        
                        
                              
                   
          

                                                      
                                                        
                        
             
          

                                                                                    
                                          
                
                               
                      
          

                                                                                    
                                          
                
                                                          
                           
          

                                                                             

                                                                                             

                                                                                          

                                                        
                                                                           
                                                     
                             
                              
                                     

                                                                
                                                       
                                                                           

                                                           
                                                                                             
                                                                                            

                                                   
                                                                    
                                                                               
                                    
                                                                                  
                                         
                                    
                                                                      
                                                             
                                                                
                                            
                                                            
                
                    

                                
                                                                           
                                     
                  
                                                                

                                                                                   

                                                                            
                                                                       
                         
                
                                                                                                   
                                       
                                                              
          

                                                                                                
                                                                         
                                                       

                                                                                    
                                    
                
                           
            
          

                                                    
                                                                                                
                       
                                                                                         
                                      
                                    
                                                                                  
                                               
                                               
                                      
                                            
                                
                                                   
                                
                                      
                               
                                            
                                     
             
            
                       
                                                              
                                                                  
                                                                
                                                                  
                                       
                                                                                             
                         
                                

                                                                                             
                                                                            
                                                                                         
                                                               
                                           
                                                                                              
                       
                                    

                           
                                                                                

                                                                        
                                     
                                                                                                     
                               
                                                             
                                           
                                     
                                           
      

                                                                                  
                                              
                                                                                  
                                                          
                                          
                                                      
                                                                     
                                                  
                                                                                 
                                                                                              
                                                                        

                                                                                      
                                                               
                                                                                         
                                     
                                                                                           
                                                      
                                                    
                                                                
             
                                             
       
                                                                                                   
                                                                                                   
                                                                    
                                                                               
           
                                                 
                                                 
                                               
                                                                                 
                                                                                  

                                                 
                                                                                               
                                              
                           
                
      

                                                              
                                                                
                                                          
                                                                                   
                                       
                                                       
                                                                           
                                                         
                                                                                                
                                                                                       
                                                           
      

end Structure

section PsiToolkit
/-! ## ψ toolkit  (generic facts about `psiA cϱ p` = min(L, 2/|r|, c/(w r²)) [eq:psidef]).
Statements are consumed by EndsE1/EndsE2. -/
variable {cϱ : ℝ} {p : Setting} {F : LocalFun}

                                              
                                                                    
                 

                                                       

                                                   
                     
                   
                                                  

                                                                                    
                                                                               

                                                                          
                                                                              

                                                              
             

                                                                                               
                     
                       
                           
                                                             


                                                            
                                
                        
                                

                               
                                                                      
                                            
                     
                                  
                                         
                                     
                                              
                                                                                         
                                               
                                                           
                                                        
                                                                     

                                      
                                                                
                                                              
                                              
                           
         

                                                                                
                                                                                     

                                                                      
                                                                                       
                                                        
                                                
                                                                            
                                                              
                                                                                    
                                                                                      
                        
                                       
                                                                       
                                         
                                                                  
                            
                                                                         
                
                              
                  

                                                              
                                                                                     
                                                                    
                                                     
                                                              
                                        

                                                                               
                                                                                           
                                                                                       
                                                                             
                                                                   
                                                 
                                                                                 
                                         
                                                                                  
              
           
                                                   
                                                                      
             
                               
                                                                             
                 
          
                           
                                               
                                                          
                                                           
                                                                                                     
                                                                                         
                                                                    
                                                                 
                                                     
                                                                                          
             
                             
                                                                                            
                                                         
                                                        
                   
                                                                                                
                      
                                                       
                                      
                                                                                                              
                                                      
                                                   
                                                                       
                                              
                                              
                                                                                                       
                                           
                
                                    
                                                                                                     
                                                  
                                         
                                                                                                   
                                                                        

                                                                                      
                                                                                                   
                                               
                                                            
                           
                                                                                           
                                                                           

                                                
                                                         
                                                           
                                                 
                                                
                     
                                                       
                                        
                                                  

                                                                   
                                                                                                      
                                                   
                                                                    
                                                                                   
                                                                      

                                                            
                                                                                          
                                                                          
                                                
                                                 
                                                                                  
                                                              
                                                                                              
                                                                                         
                        
                                       
                                                                            
                                                                                                      
                                               
                                                                                                
                        
                                          
                                                                         
                
                  

                                  
                                                                         
                                                  
                                                        
                                                                             

                                                      
                                                                                               
                    

                                                            
                                                       
                                                                          
                                                                     

end PsiToolkit

section Kbounds
/-! ## [eq:Kbounds] pointwise (§5.3) -/
variable {cϱ : ℝ} {p : Setting} {F : LocalFun}


                                                           
                                                                
                                                             
                                                                                    
                                                                                          
         
                                                                  
               
                     
                                         
                         
            
                                                              

                                                         
                                                                          
                          
                                 
                                                                                      
                                         
           
                                                            

                                                                                  
                                                                             
            
                                
                                                                                            
                                                 
                            
          

                                                                                       
                                             
                                                         
                                                                                        
                       
                                
                                                                                
                                      
                                                                                    
                           
              
                       
        
         
            

                                                                                               
                                                                                             
                                                        
                                                                                            
                                                                                        
           
                              
                    
            
                                                              
                                            
                                          
                                                       
                                                    
               
                                                                              
                                                     
                                                               
                                  
                                                                                     
                                      
                                                                               

                                                             
                                                                                             
                     
             
                                 
                                                       

                                                                        
                                                                      
                                                                                             
             
                                                                                   
              
                     
                                                
                                                 
                                                                           
                               

                                                   

                                                                                    
                                                  
                                                                            
                                                           
                                                                                      
         
                                                                  
               
                     
                                         
                         
            
                                                              

                                                                               
                                                             
                                                            
                                                       
                                           
                                                                                    
                                        
                                                                                                      
                                      
                                         
                                                                                          
                           
                                                                                                 
        
         
            

                                                                      
                                                          
                                               
              
                                                       
                                                                                  
                       
                       
              
                      
                  

                                                                      
                                                  
                                                                                           
                                                                                
                                                      
                                                                     
                                
                            
                              
             
                                                                      
                                                                             
                                               
                                                       
                                                                                                   
                                       
                                          
                                                                      
                   
                                      
                                                                                        
                                           
                                               
                                      

end Kbounds


end PrimeSide
end Zeta23
