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

                                        
                                                           

                                                     
                                                     

                                                               

                                                                   
                                                                                      
                                                                                       
                                                                                      
                                                                                        
  

                                                                    
                                                                        
                     
                                                                        
                                      

                                                                               
                                                                                    
def PiX (X : ℝ) (τ : ℝ) : ℝ :=
  let s : ℂ := 1 / 2 + Complex.I * τ
  1 / (2 * Real.pi * (1 / 4 + τ ^ 2)) + (1 / Real.pi) * (((X : ℂ) ^ s - 1) / s).re

                                                                                                    
                                                                                                
                             
                                                                                           

                                        
                                                      

                                                                                         

                                                                                                 
                        
def gammaOf (ρ : ℂ) : ℂ := (ρ - 1 / 2) / Complex.I

/-- The reflection ρ ↦ 1 − ρ̄ (same ordinate γ, mirrored β)  [subsec:weil]. -/
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

/-- on-line points: β = 1/2. -/
def onLine : Set ℂ := {ρ | ρ.re = 1 / 2}

/-- simple points: m_ρ = 1. -/
def simple : Set ℂ := {ρ | Z.mult ρ = 1}

                                                                           
                                                        

                                                                       
                                                

                                                                                              
                                                                  

                                                                                                  
                                                             

                                                                     
                                                                     

                                                                               
                                                           

                                                                           
def Wsummand (f g : ℝ → ℂ) (ρ : ℂ) : ℂ :=
  (Z.mult ρ : ℂ) * paperFT f (gammaOf ρ) * (starRingEnd ℂ) (paperFT g ((starRingEnd ℂ) (gammaOf ρ)))

/-- W(f,g) := Σ_ρ m_ρ h_f(γ_ρ) conj(h_g(conj γ_ρ)), "Σ_ρ runs over the DISTINCT nontrivial zeros (of
either sign of γ) and the multiplicity is written explicitly"  [eq:Wdef]. As a tsum over the
subtype of carrier; absolute convergence is part of hypothesis H-EF. -/
def W (f g : ℝ → ℂ) : ℂ := ∑' ρ : Z.carrier, Z.Wsummand f g ρ

end ZeroConfig

/-! ## 4. The test family  [subsec:family] -/

/-- "Fix once and for all a nondecreasing function ϱ ∈ C³(ℝ) with ϱ = 0 on (−∞,0] and ϱ = 1 on
[1,∞)"  [subsec:family]. -/
structure TaperProfile (ϱ : ℝ → ℝ) : Prop where
  contDiff : ContDiff ℝ 3 ϱ
  monotone : Monotone ϱ
  eq_zero : ∀ x ≤ 0, ϱ x = 0
  eq_one : ∀ x ≥ 1, ϱ x = 1

/-- Fixed (T-independent) parameters: the profile ϱ, the exponent λ (lam; X = (T/2π)^λ), and the
ramp width w ([eq:wrange]: 1 ≤ w ≤ L/8; §6 takes w := 1). T is always a separate argument. -/
structure Params where
  ϱ : ℝ → ℝ
  lam : ℝ
  w : ℝ

/-- Standing assumptions on the fixed parameters: ϱ a taper profile, 0 < λ ≤ 1, w ≥ 1.
(The upper bound w ≤ L/8 of [eq:wrange] depends on T and is stated where used.) -/
structure Params.Valid (P : Params) : Prop where
  taper : TaperProfile P.ϱ
  lam_pos : 0 < P.lam
  lam_le_one : P.lam ≤ 1
  one_le_w : 1 ≤ P.w

namespace Params

variable (P : Params) (T : ℝ)

/-- L := λ·l  [Notation]. -/
def L : ℝ := P.lam * l T

/-- X := e^L = (T/2π)^λ  [Notation]. -/
def X : ℝ := Real.exp (P.L T)

                                                                          
                              

                                    
def hgrid : ℝ := 2 * Real.pi / P.L T

/-- d := ⌊T/h⌋ = ⌊LT/2π⌋  [eq:fk]. -/
def d : ℕ := ⌊P.L T * T / (2 * Real.pi)⌋₊

/-- τ_k := T + k h (k ∈ ℤ)  [eq:fk]. -/
def tau (k : ℤ) : ℝ := T + k * P.hgrid T

/-- the taper φ(u) := ϱ((L/2 − |u|)/w)  [eq:phidef]; supp φ = [−L/2, L/2] exactly. -/
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

                                                                                            
                                                                                      
                                                     

                                                                                       
                                                                                      
                     

                                                                              
def S1 (Z : ZeroConfig) (T : ℝ) : Set ℂ := Z.ZIprime T ∩ onLine ∩ Z.simple
/-- 𝒮₂: β = 1/2 and m_ρ ≥ 2, within 𝒵(I'). s₂ := #𝒮₂. -/
def S2 (Z : ZeroConfig) (T : ℝ) : Set ℂ := Z.ZIprime T ∩ onLine ∩ {ρ | 2 ≤ Z.mult ρ}
/-- off-line points of 𝒵(I') (β ≠ 1/2); 𝒫 = unordered pairs {ρ, 1−ρ̄} of these, #offLine = 2p. -/
def offLine (Z : ZeroConfig) (T : ℝ) : Set ℂ := Z.ZIprime T ∩ {ρ | ρ.re ≠ 1 / 2}

                 
                                                     
                 
                                                     
                                                                                
def p (Z : ZeroConfig) (T : ℝ) : ℕ := (Z.offLine T).ncard / 2

                                            
                                                                         
                                             
                                                                            

end ZeroConfig

end Zeta23
