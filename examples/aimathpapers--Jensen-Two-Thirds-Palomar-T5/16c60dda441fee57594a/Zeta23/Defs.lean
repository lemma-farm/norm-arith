/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/Defs.lean — fixed data of the paper.

Reference text: the paper "More than two thirds of the zeros of the Riemann zeta function lie on
the critical line". Bracketed labels [eq:foo] below are the paper's own labels.

Design (ζ-free abstract layer): nothing in this file mentions
riemannZeta. The zeros enter only through the abstract structure ZeroConfig
("every locally finite multiset of points in the strip 0<β<1 that is invariant under ρ ↦ 1−ρ̄",
paper end of §4). Only Zeta23/Statement.lean instantiates ZeroConfig from Mathlib's ζ.
-/
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Data.Set.Card
import Mathlib.Data.Matrix.Basic

open scoped BigOperators ArithmeticFunction
open Complex MeasureTheory Set

noncomputable section

namespace Zeta23

/-! ## 0. Fourier convention dictionary  [Notation], [subsec:weil]

Paper: "Fourier transforms are f̂(τ) := ∫_ℝ f(u) e^{iτu} du, so that ∫ f ḡ = (1/2π) ∫ f̂ conj(ĝ)
and (f∗g)^ = f̂ ĝ."  and  "For f ∈ C_c²(ℝ) put h_f(z) := f̂(z) = ∫ f(u) e^{izu} du, an entire
function".  Mathlib's Real.fourierIntegral 𝓕 is ∫ f(v) e^{−2πi v ξ} dv, so for real τ:
    paperFT f τ = 𝓕 f (−τ / (2π)).
All paper-side statements use paperFT; conversion to 𝓕 happens only inside proofs. -/

/-- Paper Fourier transform / h_f :  paperFT f z = ∫ u, f u * exp (I * z * u)  for complex z
([Notation]; [subsec:weil] "h_f(z) := f̂(z) = ∫ f(u)e^{izu} du"). -/
def paperFT (f : ℝ → ℂ) (z : ℂ) : ℂ := ∫ u : ℝ, f u * Complex.exp (Complex.I * z * (u : ℂ))

/-! ## 1. Scalars depending on T only  [Notation], [eq:RvM], [eq:Fdef] -/

/-- l := log(T/2π)  [Notation]. -/
def l (T : ℝ) : ℝ := Real.log (T / (2 * Real.pi))

                                                                            
                                                

                                                    
                                         

                                                     
                                           

                              
def D0 (T : ℝ) : ℝ := Real.sqrt T

/-- I := [T, 2T]  [Notation]. -/
def Iwin (T : ℝ) : Set ℝ := Icc T (2 * T)

                                        
                                                           

                                                     
                                                     

                                                               

                                                                   
                                                                                      
                                                                                       
                                                                                      
                                                                                        
  

                                                                    
                                                                        
                     
                                                                        
                                      

                                                                               
                                                                                    
                              
                                    
                                                                                  

                                                                                                    
                                                                                                
                             
                                                                                           

                                        
                                                      

                                                                                         

                                                                                                 
                        
                                                  

                                                                              
def reflect (ρ : ℂ) : ℂ := 1 - (starRingEnd ℂ) ρ

/-- An abstract zero configuration: a set (carrier) of DISTINCT points ρ = β+iγ in the closed
strip 0 ≤ β ≤ 1 (the instances built from the zeros of ζ and of L(s,χ) lie in the open strip) with
multiplicities mult ρ ≥ 1, locally finite in the ordinate, and
invariant under ρ ↦ 1−ρ̄ with equal multiplicity. Paper §4 (after prop:zeroside), verbatim:
"Inequalities (eq:zeroside) hold for every locally finite multiset of points in the strip 0<β<1
that is invariant under ρ ↦ 1−ρ̄ and satisfies N(t+1)−N(t) ≪ log(t+3); they contain no
arithmetic."  [subsec:weil]: "The multiset {(γ_ρ,m_ρ)} is invariant under γ ↦ γ̄ (i.e. ρ ↦ 1−ρ̄;
multiplicities agree …)".  The quantitative local count N(t+1)−N(t) ≤ A₀ log(t+3) is not part of
this structure; it is a field of PaperInputs (H-RvM) in Zeta23/Hypotheses.lean.
Distinct points (the set) and multiplicities (the function) are deliberately separate objects. -/
structure ZeroConfig where
  /-- the set 𝒵 of distinct zeros -/
  carrier : Set ℂ
  /-- multiplicity m_ρ (value irrelevant off carrier) -/
  mult : ℂ → ℕ
  one_le_mult : ∀ ρ ∈ carrier, 1 ≤ mult ρ
  strip : ∀ ρ ∈ carrier, 0 ≤ ρ.re ∧ ρ.re ≤ 1
  reflect_mem : ∀ ρ ∈ carrier, reflect ρ ∈ carrier
  mult_reflect : ∀ ρ ∈ carrier, mult (reflect ρ) = mult ρ
  /-- local finiteness in the ordinate: finitely many zeros with T₁ < γ ≤ T₂ -/
  finite_window : ∀ T₁ T₂ : ℝ, (carrier ∩ {ρ | T₁ < ρ.im ∧ ρ.im ≤ T₂}).Finite

namespace ZeroConfig

variable (Z : ZeroConfig)

/-- {ρ ∈ 𝒵 : T₁ < γ ≤ T₂}, γ = Im ρ (positive-ordinate window convention of [Results]; NOT |γ|). -/
def window (T₁ T₂ : ℝ) : Set ℂ := Z.carrier ∩ {ρ | T₁ < ρ.im ∧ ρ.im ≤ T₂}

                               
                                        

                              
                                        

                                                                           
                                                        

                                                                       
                                                

                                                                                              
                                                                  

                                                                                                  
                                                             

                                                                     
                                                                     

                                                                               
                                                           

                                                                           
                                         
                                                                                                    

                                                                                                    
                                                                                            
                                                                       
                                                             

end ZeroConfig

/-! ## 4. The test family  [subsec:family] -/

                                                                                              
                           
                                               
                           
                       
                            
                           

                                                                                                
                                                                                             
structure Params where
  ϱ : ℝ → ℝ
  lam : ℝ
  w : ℝ

                                                                                      
                                                                                  
                                                
                          
                     
                        
                    

namespace Params

variable (P : Params) (T : ℝ)

/-- L := λ·l  [Notation]. -/
def L : ℝ := P.lam * l T

/-- X := e^L = (T/2π)^λ  [Notation]. -/
def X : ℝ := Real.exp (P.L T)

                                                                          
                              

                                    
                                    

                                     
                                         

                                       
                                        

                                                                                     
def phi (u : ℝ) : ℝ := P.ϱ ((P.L T / 2 - |u|) / P.w)

/-- a := L⁻¹ ∫ φ²  [eq:abdef]. -/
def a : ℝ := (P.L T)⁻¹ * ∫ u : ℝ, (P.phi T u) ^ 2

/-- b := L⁻¹ ∫ φ⁴  [eq:abdef]. -/
def b : ℝ := (P.L T)⁻¹ * ∫ u : ℝ, (P.phi T u) ^ 4

/-- φ̂(z) for complex z (paper convention, = h_φ(z)). -/
def phiHat (z : ℂ) : ℂ := paperFT (fun u => (P.phi T u : ℂ)) z

                                                                                             
                                                                         
                                                  

                                                
def Phi (z : ℂ) : ℂ := paperFT (fun u => (((P.phi T u) ^ 2 : ℝ) : ℂ)) z

                                                      
                                            

                                                  
def autocorr (v : ℝ → ℝ) (y : ℝ) : ℝ := ∫ u : ℝ, v u * v (u + y)

/-- g := φ² ⋆ φ²  [eq:PhigA]; Φ² = ĝ on ℝ, g(0) = bL. -/
def g (y : ℝ) : ℝ := autocorr (fun u => (P.phi T u) ^ 2) y

/-- A_φ := φ ⋆ φ  [eq:PhigA]; φ̂² = (A_φ)^. -/
def Aphi (y : ℝ) : ℝ := autocorr (P.phi T) y

                                                     
               
                                                                   

                                                                                                    
                                                           
                                                                                                    

                                                                     
                                                                                          

                                                                      
               
                                                                                    

                                                                 

                                                                                                     
                                                   
                           
                                                                                    

                                                                                           
                                                                                     
                                                
                                             

                                                                                    
                                                                 

                                                                                    
                                                                                              

                                                                      
                                                                              

                                                                                          
         
                                                                                        

end Params

/-! ### The zero-side matrices  [eq:Gdef] first expression, [eq:AE], §4 Block structure -/

namespace ZeroConfig

                                                         
                                                                           
                                                                                          

                                                                                                 
                                                               
                                                                                      
                                                   

                                                                                          
def ZIprime (Z : ZeroConfig) (T : ℝ) : Set ℂ := Z.window (T - D0 T) (2 * T + D0 T)

                                                                                            
                                                                                      
                                                     

                                                                                       
                                                                                      
                     

                                                                              
                                                                          
                                                        
                                                                                    
                                                                                                 
def offLine (Z : ZeroConfig) (T : ℝ) : Set ℂ := Z.ZIprime T ∩ {ρ | ρ.re ≠ 1 / 2}

                 
                                                     
                 
                                                     
                                                                                
def p (Z : ZeroConfig) (T : ℝ) : ℕ := (Z.offLine T).ncard / 2

                                            
                                                                         
                                             
                                                                            

end ZeroConfig

end Zeta23
