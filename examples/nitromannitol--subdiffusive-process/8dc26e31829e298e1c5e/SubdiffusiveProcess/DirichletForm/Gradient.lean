/-
# Gradient-type energies and their Markov property
-/
module

public import SubdiffusiveProcess.DirichletForm.Basic
public import Mathlib

@[expose] public section

/-!
# Gradient-type energies and their Markov property

Most concrete Dirichlet forms are given by a *gradient energy*

`E(u) = ∫ q(x, ∇u(x)) dμ(x)`

with `q(x, ·)` nonnegative and homogeneous of degree two — for a divergence-form
operator, `q(x, ξ) = ⟪A(x) ξ, ξ⟫`.  For such a form the Markov property is an
immediate consequence of one analytic fact: composition with a normal
contraction `T` keeps the element in the space and replaces the gradient by
`T'(u) ∇u`, with `|T'| ≤ 1` (Stampacchia).

Mathlib 4.26 has **no** Sobolev space and no weak-gradient chain rule (the only
Sobolev file is `Mathlib/Analysis/FunctionalSpaces/SobolevInequality.lean`, the
Gagliardo–Nirenberg–Sobolev inequality), so that fact is stated here as the
`Prop`-valued external input `SubdiffusiveProcess.DirichletForm.HasContractionChainRule`.  It is not
an axiom; it is passed as a hypothesis, exactly like the other inputs of this
library.

Given the input, `SubdiffusiveProcess.DirichletForm.GradientEnergy.exists_comp_energy_le` and
`SubdiffusiveProcess.DirichletForm.ClosedForm.isMarkovian_of_gradientEnergy` are **proved**: the
energy does not increase under a normal contraction, and a closed form whose
energy is a gradient energy is Markovian.

## References

* G. Stampacchia, *Le problème de Dirichlet pour les équations elliptiques du
  second ordre à coefficients discontinus*, Ann. Inst. Fourier 15 (1965)
  (truncation of Sobolev functions).
* Fukushima–Oshima–Takeda, *Dirichlet Forms and Symmetric Markov Processes*,
  Example 1.2.3 and Theorem 1.4.1.
-/

open MeasureTheory Filter Topology

noncomputable section

namespace SubdiffusiveProcess.DirichletForm

variable {X : Type*} [MeasurableSpace X]

/-- A **gradient energy structure** on a type `H`: every element has a value
(a function on `X`) and a gradient (a `V`-valued function on `X`), and its energy
is the `μ`-integral of a nonnegative, degree-two homogeneous integrand of the
gradient.

Inhabited by: `SubdiffusiveProcess.DirichletForm.zeroGradientEnergy`. The witness establishes
NON-VACUITY only; inhabitation at the paper's form is the external input
`SubdiffusiveProcess.DirichletForm.HasEnergyMeasure`. -/
structure GradientEnergy (μ : Measure X) (V : Type*) [SMul ℝ V] (H : Type*) where
  /-- The value of an element, as a function on `X`. -/
  value : H → X → ℝ
  /-- The gradient of an element. -/
  grad : H → X → V
  /-- The energy integrand `q(x, ξ)`. -/
  integrand : X → V → ℝ
  /-- The energy `E(u) = ∫ q(x, ∇u x) dμ`. -/
  energy : H → ℝ
  /-- `q(x, ξ) ≥ 0`. -/
  integrand_nonneg : ∀ (x : X) (ξ : V), 0 ≤ integrand x ξ
  /-- `q(x, cξ) = c² q(x, ξ)`: the integrand is a quadratic form in the
  gradient. -/
  integrand_smul : ∀ (x : X) (c : ℝ) (ξ : V), integrand x (c • ξ) = c ^ 2 * integrand x ξ
  /-- The energy is the integral of the integrand of the gradient. -/
  energy_eq : ∀ u : H, energy u = ∫ x, integrand x (grad u x) ∂μ
  /-- The integrand of the gradient is integrable. -/
  integrable : ∀ u : H, Integrable (fun x => integrand x (grad u x)) μ

                                                                               
                                                                                
                                                                               
                                                                  

                                                                           
                                 
                                                                             

                                                                            
                                                                            
                                                                                          
                                                       

                                                                                          
                                                                              
                                                              
                                                                                    
                                                           
                                                                     
                                                              
                                                 
                                                    
                                                  

namespace GradientEnergy

variable {μ : Measure X} {V : Type*} [SMul ℝ V] {H : Type*} (G : GradientEnergy μ V H)

                                                                         
          
                                                                              
                                                                                        
                                                  
                                                               
                                    
                             
                                                          
                                                                                
                             
                
                                              
                                               

                                                                              
                                                                            
                                                                            
                                                                                    
                                                      
                                                                                         
                                                             
                                                    

end GradientEnergy

namespace ClosedForm

                                                                        
                                                                   
                                                                                 
                                                                        
                                                                
                                       
                                                 
                                                 
                                                              
                       
                      
                               
                                                                
                                     
                                                                       
                            
                                              
                            
                             
           

end ClosedForm

end SubdiffusiveProcess.DirichletForm
