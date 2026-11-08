/-
# Energy measures of a strongly local Dirichlet form
-/
module

public import SubdiffusiveProcess.DirichletForm.Killed
public import Mathlib
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic

@[expose] public section

/-!
# Energy measures

For a regular strongly local Dirichlet form `E` on `L²(X, m)` the *energy
measure* (carré du champ) `Γ(u)` of `u ∈ D(E)` is the finite Borel measure with
`∫ φ dΓ(u) = E(u, uφ) - ½ E(u², φ)`; the polarized cross measure `Γ(u, v)` is a
signed measure.  This file carries the calculus of these measures as a structure
`SubdiffusiveProcess.DirichletForm.EnergyMeasure`, whose fields are exactly the properties used in
applications: total mass, bilinearity, Cauchy–Schwarz, locality on open sets,
the chain rule and the Leibniz rule.

Existence of an energy measure is **not proved here**.  It is an accepted
external input, recorded as the `Prop`-valued structure
`SubdiffusiveProcess.DirichletForm.HasEnergyMeasure`, together with the algebra property of the core
(`SubdiffusiveProcess.DirichletForm.IsCoreAlgebra`).  Neither is an axiom; both are passed as
hypotheses.

## References

* M. Fukushima, Y. Oshima, M. Takeda, *Dirichlet Forms and Symmetric Markov
  Processes*, 2nd edition, §3.2 (Theorem 3.2.2, Lemma 3.2.5) and Theorem 1.4.2.
* A. Beurling, J. Deny, *Dirichlet spaces*, Proc. Nat. Acad. Sci. 45 (1959).
-/

open MeasureTheory Filter Topology
open scoped ContDiff

noncomputable section

variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X] {m : Measure X}

namespace SubdiffusiveProcess.DirichletForm

/-- Integral of a real function over a set against a signed measure, through the
Jordan decomposition. -/
def signedIntegralOn (ν : SignedMeasure X) (B : Set X) (f : X → ℝ) : ℝ :=
  (∫ x in B, f x ∂ν.toJordanDecomposition.posPart) -
    (∫ x in B, f x ∂ν.toJordanDecomposition.negPart)

                            
                                                                              
                                                                                
                              
                                                                     

                            
                                                                         
                                               
                         

                            
                                                                            
                                                                        
                                            
      

                            
                                                                             
                                                                            
                            
                                                                                    
                              
                                                             
                                                         
                                                          
      

                                                                              
                                                                            
                                                                   

                                                                               
                                                                           
                                                                                 
                                                                                   
                                                                             
                                                                             
                                                                            

                                                                                            
                                                                        
                                                        
structure EnergyMeasure (E : ClosedForm m) where
  /-- The energy measure `Γ(u)`. -/
  measure : Lp ℝ 2 m → Measure X
  /-- The cross energy measure `Γ(u, v)`. -/
  cross : Lp ℝ 2 m → Lp ℝ 2 m → SignedMeasure X
  /-- `Γ(u)` is a finite measure for `u ∈ D(E)`. -/
  measure_univ_lt_top : ∀ u ∈ E.domain, measure u Set.univ < ⊤
  /-- `Γ(u)(X) = E(u, u)`. -/
  measure_univ : ∀ u ∈ E.domain, (measure u Set.univ).toReal = E.form u u
  /-- `Γ(u, v) = Γ(v, u)` for `u, v ∈ D(E)`. -/
  cross_symm : ∀ u ∈ E.domain, ∀ v ∈ E.domain, cross u v = cross v u
  /-- `Γ(u, u) = Γ(u)`. -/
  cross_self : ∀ u ∈ E.domain, ∀ B : Set X, MeasurableSet B →
    cross u u B = (measure u B).toReal
  /-- `Γ` is additive in its second argument, on `D(E)`. -/
  cross_add_right : ∀ u ∈ E.domain, ∀ v ∈ E.domain, ∀ w ∈ E.domain,
    cross u (v + w) = cross u v + cross u w
  /-- `Γ` is homogeneous in its second argument, on `D(E)`. -/
  cross_smul_right : ∀ (c : ℝ), ∀ u ∈ E.domain, ∀ v ∈ E.domain,
    cross u (c • v) = c • cross u v
  /-- `Γ(u, v)(X) = E(u, v)`. -/
  cross_univ : ∀ u ∈ E.domain, ∀ v ∈ E.domain, cross u v Set.univ = E.form u v
  /-- Cauchy–Schwarz for the cross measure, on `D(E)`. -/
  abs_cross_le : ∀ u ∈ E.domain, ∀ v ∈ E.domain, ∀ B : Set X, MeasurableSet B →
    |cross u v B| ≤
      Real.sqrt (measure u B).toReal * Real.sqrt (measure v B).toReal
  /-- Locality: `Γ(u)` and `Γ(w)` agree **as measures restricted to** an open set
  on which `u = w`, for `u, w ∈ D(E)`.

  The paper's display is the total mass
  `Γ(u)(O) = Γ(w)(O)`, which is recovered as `locality_apply` below.  The
  restricted form is what Fukushima–Oshima–Takeda Theorem 3.2.2 gives (`Γ` is a
  local functional) and it is what the paper's own use at  needs: there
  `Γ(w_ε)` is identified with `1_{q ∩ {|v|>ε}} Γ(v)` as measures, which the
  total-mass version cannot deliver. -/
  locality : ∀ u ∈ E.domain, ∀ w ∈ E.domain, ∀ O : Set X, IsOpen O →
    (⇑u =ᵐ[m.restrict O] ⇑w) → (measure u).restrict O = (measure w).restrict O
  /-- `Γ(u)` is a Radon measure.  Fukushima–Oshima–Takeda's energy measures are
  Radon; without it the passage from test functions to Borel sets fails (doubled-space counterexample). -/
  regular : ∀ u ∈ E.domain, (measure u).Regular
  /-- `Γ(u)` is carried by the support of `u`. -/
  measure_compl_tsupport : ∀ u : Lp ℝ 2 m, u ∈ E.domain →
    ∀ f : X → ℝ, Continuous f → (⇑u =ᵐ[m] f) → measure u (tsupport f)ᶜ = 0
  /-- Chain rule `Γ(Φ(u)) = Φ'(u)² Γ(u)` for `Φ ∈ C¹` with `Φ 0 = 0`.  The
  integrand is evaluated on a continuous representative `uc` of `u`: energy
  measures need not be absolutely continuous with respect to `m`, so the
  representative is part of the statement. -/
  chain_rule : ∀ u ∈ E.domain, ∀ uc : X → ℝ, Continuous uc → (⇑u =ᵐ[m] uc) →
    ∀ Φ : ℝ → ℝ, ContDiff ℝ 1 Φ → Φ 0 = 0 →
    ∀ w ∈ E.domain, (⇑w =ᵐ[m] fun x => Φ (uc x)) →
    ∀ B : Set X, MeasurableSet B →
      (measure w B).toReal = ∫ x in B, (deriv Φ (uc x)) ^ 2 ∂(measure u)
  /-- Leibniz rule
  `Γ(vΦ(u)) = v²Φ'(u)²Γ(u) + 2vΦ(u)Φ'(u)Γ(u,v) + Φ(u)²Γ(v)` for core `u, v` and
  `Φ ∈ C¹`, evaluated on continuous representatives `uc`, `vc`. -/
  leibniz : ∀ u v : Lp ℝ 2 m, E.MemCore u → E.MemCore v →
    ∀ uc vc : X → ℝ, Continuous uc → Continuous vc → (⇑u =ᵐ[m] uc) → (⇑v =ᵐ[m] vc) →
    ∀ Φ : ℝ → ℝ, ContDiff ℝ 1 Φ →
    ∀ w ∈ E.domain, (⇑w =ᵐ[m] fun x => vc x * Φ (uc x)) →
    ∀ B : Set X, MeasurableSet B →
      (measure w B).toReal =
        (∫ x in B, (vc x) ^ 2 * (deriv Φ (uc x)) ^ 2 ∂(measure u)) +
          2 * signedIntegralOn (cross u v) B
              (fun x => vc x * Φ (uc x) * deriv Φ (uc x)) +
          (∫ x in B, (Φ (uc x)) ^ 2 ∂(measure v))
  /-- The identity that DEFINES the energy measure
  (`mfd:prop-killed-consistency`): `∫ φ dΓ(u) = E(u, uφ) - ½ E(u², φ)` for a
  core function `u` and a core test function `φ`.  It is what makes `Γ(u)`
  unique, and it is what `mfd:lem-borel-weights` consumes. -/
  defining_identity : ∀ u φ : Lp ℝ 2 m, E.MemCore u → E.MemCore φ →
    ∀ uc φc : X → ℝ, Continuous uc → Continuous φc →
      (⇑u =ᵐ[m] uc) → (⇑φ =ᵐ[m] φc) →
    ∀ uφ u2 : Lp ℝ 2 m, uφ ∈ E.domain → u2 ∈ E.domain →
      (⇑uφ =ᵐ[m] fun x => uc x * φc x) → (⇑u2 =ᵐ[m] fun x => uc x ^ 2) →
      (∫ x, φc x ∂(measure u)) = E.form u uφ - (1 / 2 : ℝ) * E.form u2 φ

namespace EnergyMeasure

variable {E : ClosedForm m} (Γ : EnergyMeasure E)

                                 
                                                    
                                                                               
                                                              
                                       
                                          
                                                     
                                              

                                                        
                                                                                 
                                                                             
                                                                                     
                                                   

                                                           
                                                                    
                                                                   
                                                                                   
                           

                                                                  
                                                                                     
                 
                               
                                                             
                                    
                                            
                                                                       
                                                 
      

                                                                  
                                                                                     
                 
                               
                                                             
                                                              
                                                                             
                                                                          
                                                                     
                                       
                                          
      

                                                             
                                                                                      
                 
                   
                                                                       
                                                                 
      

                                                     
                                                                       
                        
                                                                                

                                                                       
                                                   

                                        
                                                                        
                                                    
                             
                             

                                                                             
                                                                            
                                                                      
                                                                

                                                     
                                                                               
                                             
                            
                                                    

                                                                              
                                                                                
                                                                              
                                                                            
                                                                            
                             
                                                                         
                                                                               
                                                                   
                                                                  
                                             
                                            
                                                                
                                                                                        
                                                                                       

end EnergyMeasure

                                                                         
                                                                       
                                                                         
                                                                         
                      

                                                             

                                                                               
                                                                               
                                                                                            

                                                                                            
                                                                        
                                                        
                                                       
                                                                               
                                                                            
                                 
                         
                                           
                                                         
                                                               
                                                                                   
                                                                                  
                                                             
                                                                                    
                                                                                
                                                                                    
                                                                 
                                                                         
                                                                             
                                                                        
                                                        
                                                                       
                             
                                                                     
                                                                                  
                                                                   
                                                                     

end SubdiffusiveProcess.DirichletForm

                                                                            
                                                                                 
                                                                                        

                                                                             
                                                     

                                                                                 
                                                                                 
                                                                               
                       

                                                                                               
                                                                        
                                                        
                                                                                            
                                                                                                      
                                                                           
                                                                                            
                                                                             
                                                                                    
