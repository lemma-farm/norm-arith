/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import MarkovProcess.Semigroup.Basic
                                                  
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The generator of a strongly continuous contraction semigroup

For `S : StronglyContinuousContractionSemigroup E` this file defines the generator domain
`S.generatorDomain`, the submodule of vectors `f` whose difference quotients
`t⁻¹ • (S t f - f)` converge as `t → 0⁺`, and the generator
`S.generator : S.generatorDomain →ₗ[ℝ] E` as that limit.  The main results are:

* `tendsto_generator`: the defining limit, and `generator_eq_of_tendsto`, its uniqueness;
* `operator_mem_generatorDomain` and `generator_operator`: the domain is invariant under every
  `S t`, and `S t` commutes with the generator;
* `tendsto_differenceQuotient_add`: every orbit `t ↦ S t f` of a vector in the domain is right
  differentiable at every time, with derivative `S t (S.generator f)`; its real-variable forms are
  `hasDerivWithinAt_Ioi` and `hasDerivWithinAt_Ici`, and at positive times the derivative is
  two-sided, `hasDerivAt_operator_toNNReal`;
* `operator_sub_eq_integral` and `exp_smul_operator_sub_eq_integral`: the fundamental identity
  and its exponentially weighted form;
* `orbitIntegral_mem_generatorDomain` and `generator_orbitIntegral`: for every vector `f`, the
  orbit integral `∫₀ᵗ S s f ds` lies in the domain with generator `S t f - f`; hence
  `dense_generatorDomain`, the domain is dense.

Times are `NNReal` throughout the library; the real-variable statements read the semigroup at
`Real.toNNReal s`.  The fundamental identity is what Dynkin's formula consumes.
-/

open Filter Topology
open scoped NNReal

namespace MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (S : StronglyContinuousContractionSemigroup E)

section DifferenceQuotient

/-- The difference quotient `t⁻¹ • (S t f - f)` of the orbit of `f` at time zero. -/
def differenceQuotient (f : E) (t : NNReal) : E := (t : ℝ)⁻¹ • (S t f - f)

/-- The difference quotient, unfolded. -/
theorem differenceQuotient_apply (f : E) (t : NNReal) :
    S.differenceQuotient f t = (t : ℝ)⁻¹ • (S t f - f) := rfl

/-- Difference quotients are additive in the vector. -/
theorem differenceQuotient_add (f g : E) (t : NNReal) :
    S.differenceQuotient (f + g) t = S.differenceQuotient f t + S.differenceQuotient g t := by
  rw [differenceQuotient, differenceQuotient, differenceQuotient, map_add, add_sub_add_comm,
    smul_add]

/-- Difference quotients are homogeneous in the vector. -/
theorem differenceQuotient_smul (c : ℝ) (f : E) (t : NNReal) :
    S.differenceQuotient (c • f) t = c • S.differenceQuotient f t := by
  rw [differenceQuotient, differenceQuotient, map_smul, ← smul_sub, smul_comm]

/-- The difference quotient of the zero vector vanishes. -/
theorem differenceQuotient_zero (t : NNReal) : S.differenceQuotient 0 t = 0 := by
  rw [differenceQuotient, map_zero, sub_zero, smul_zero]

/-- The operator `S s` commutes with difference quotients. -/
theorem differenceQuotient_operator (f : E) (s t : NNReal) :
    S.differenceQuotient (S s f) t = S s (S.differenceQuotient f t) := by
  rw [differenceQuotient, differenceQuotient, map_smul, map_sub, S.commute_apply]

end DifferenceQuotient

section Domain

/-- The generator domain of `S`: the vectors whose difference quotients `t⁻¹ • (S t f - f)`
converge as `t → 0⁺`.  It is a linear subspace of `E`. -/
def generatorDomain : Submodule ℝ E where
  carrier := {f | ∃ g : E, Tendsto (S.differenceQuotient f) (𝓝[>] 0) (𝓝 g)}
  add_mem' := by
    rintro f g ⟨a, ha⟩ ⟨b, hb⟩
    refine ⟨a + b, (ha.add hb).congr fun t ↦ ?_⟩
    exact (S.differenceQuotient_add f g t).symm
  zero_mem' := by
    refine ⟨0, ?_⟩
    have hzero : S.differenceQuotient 0 = fun _ ↦ 0 := funext (S.differenceQuotient_zero)
    rw [hzero]
    exact tendsto_const_nhds
  smul_mem' := by
    rintro c f ⟨a, ha⟩
    refine ⟨c • a, (ha.const_smul c).congr fun t ↦ ?_⟩
    exact (S.differenceQuotient_smul c f t).symm

/-- Membership in the generator domain, unfolded. -/
theorem mem_generatorDomain_iff {f : E} :
    f ∈ S.generatorDomain ↔ ∃ g : E, Tendsto (S.differenceQuotient f) (𝓝[>] 0) (𝓝 g) :=
  Iff.rfl

                                                                                 
                                                
                                                                             
                            
        

end Domain

section Generator

/-- The limit of the difference quotients, for a vector of the domain. -/
private noncomputable def generatorFun (f : S.generatorDomain) : E :=
  limUnder (𝓝[>] (0 : NNReal)) (S.differenceQuotient f)

private theorem tendsto_generatorFun (f : S.generatorDomain) :
    Tendsto (S.differenceQuotient f) (𝓝[>] 0) (𝓝 (S.generatorFun f)) :=
  tendsto_nhds_limUnder (S.mem_generatorDomain_iff.mp f.2)

private theorem generatorFun_eq_of_tendsto (f : S.generatorDomain) {g : E}
    (h : Tendsto (S.differenceQuotient f) (𝓝[>] 0) (𝓝 g)) : S.generatorFun f = g :=
  tendsto_nhds_unique (S.tendsto_generatorFun f) h

/-- The generator of `S`, as a linear map on its domain: `S.generator f` is the limit of the
difference quotients `t⁻¹ • (S t f - f)` as `t → 0⁺`. -/
noncomputable def generator : S.generatorDomain →ₗ[ℝ] E where
  toFun := S.generatorFun
  map_add' f g := by
    apply S.generatorFun_eq_of_tendsto
    refine ((S.tendsto_generatorFun f).add (S.tendsto_generatorFun g)).congr fun t ↦ ?_
    rw [Submodule.coe_add, differenceQuotient_add]
  map_smul' c f := by
    apply S.generatorFun_eq_of_tendsto
    refine ((S.tendsto_generatorFun f).const_smul c).congr fun t ↦ ?_
    rw [Submodule.coe_smul, differenceQuotient_smul]

/-- The defining property of the generator: the difference quotients of a vector of the domain
converge to its generator. -/
theorem tendsto_generator (f : S.generatorDomain) :
    Tendsto (S.differenceQuotient f) (𝓝[>] 0) (𝓝 (S.generator f)) :=
  S.tendsto_generatorFun f

                                                                                        
                                                    
                                                                                      
                          

                                                                     
                                                               
                                                                             
                        
                                  

                                                              
                                 
                                                                             
                                                              
                               

end Generator

section Invariance

/-- The generator domain is invariant under the semigroup. -/
theorem operator_mem_generatorDomain (f : S.generatorDomain) (t : NNReal) :
    S t f ∈ S.generatorDomain := by
  refine ⟨S t (S.generator f), ?_⟩
  refine (((S t).continuous.tendsto _).comp (S.tendsto_generator f)).congr fun h ↦ ?_
  exact (S.differenceQuotient_operator f t h).symm

                                                                         
                                                                 
                                                                                       
                                 
                                                                                     
                                                  

                                                                                              
                                                                                           
                                                                             
                                                                         
                                     
                                                                                     
                                                                        
                                     

end Invariance

section RealVariable

/-- Reading `NNReal` times from the right of a real time: `y ↦ Real.toNNReal (y - t)` sends the
right neighbourhood filter of `t` to the right neighbourhood filter of `0`. -/
theorem tendsto_toNNReal_sub (t : NNReal) :
    Tendsto (fun y : ℝ ↦ Real.toNNReal (y - t)) (𝓝[>] (t : ℝ)) (𝓝[>] 0) := by
  apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
  · have h : Tendsto (fun y : ℝ ↦ Real.toNNReal (y - t)) (𝓝 (t : ℝ))
        (𝓝 (Real.toNNReal ((t : ℝ) - t))) :=
      (continuous_real_toNNReal.tendsto _).comp ((continuous_id.sub continuous_const).tendsto _)
    rw [sub_self, Real.toNNReal_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with y hy
    exact Set.mem_Ioi.mpr (Real.toNNReal_pos.mpr (sub_pos.mpr hy))

                                                                                              
                                                                             
                                            
                                                                       
                                                               
                                                              
                                      
                                                                                                
                                          
                                        
                                                  
                                                                  

                                                                         
                                              
                                                   
                                                

                                                                                    
                                                                                              
          
                                                                   
                                                                              
                               
                                         
                                                                  
         
                                                                                       
                              
            
                                                                                         
                                                
                              
                                                        
                                                               
                                               
                                                                
                              
                                                      
        
                                                 
                                                 
                                                       
                                                       

                                                                                            
                                                                                             
                                                                                                 
                                                                   
                                                                              
                            
                                         

                                                                                               
                                                                                             
                                                                                              
                                                                        
                                                                           
                                                        
                                                               
                                         
                                                
         
                                                                              
                                                                      
            
                                                                                  
                                                  
                                                                                             
                                                                                            
                            
                                                               
                                                                                
                                                                                      
                                                                   
                        
                                              
                                                               
                                                
                                                                             
                              
                                                          
                                               
        
                                                                
                                                                           
                                                   
                                                                               
                                                          

                                                                                                  
                                                                                               
                                                                                   
                                                                                                
                                                           
                                          
                                                           
                                                          

variable [CompleteSpace E]

                                                                                             
                                                                                           
                                                       
                                                                       
                                                                            
                                                                                
                                                   
                                        
                                                          
                                                                 
              
                                                        
                                          
                                                                                  
                                 
                                                             
                                                                                          
               
                                                                

                                                                                         
             
                                                                                          
                                                 
                                              
                                                                 
                                                                            
                           
                                                                             
                                                       
                                                                               
                                                      
                                        
                                                   
              
                                                            
                                              
                                                           
                                                    
                                                                         
                                   
                                                             
                                              
                                                   
                               
                   
                          
          
                                                                  
                              
                                                                          
                                          
                                   
                                                                                          
               
                                                                                   
                                            

end RealVariable

section OrbitIntegral

                                                                                                
                              
                                                                            
                              
                                                                                  
                                                     
                                                                            
                                                                 
                                                                                            
                                                              
                                          
                                           
                                                    
                                                      
                                                 
                                            
                                                        
                                            

                                                                                            
                                                    
                                                                                 

                                    
                                             
                                                                         

                                                        
                                                               
                                

variable [CompleteSpace E]

                                                                                          
                                                  
                                                               
                                                                               

                                                                               
                                                       
                                                                                     
                                                                               
                                 
                                                                       
                                                                  
                                                                          
              
                                
                                            
                
                                                                 
                                
                                                                                                     
                 
                                                                  
                          
                                                                                   
                                           
                                                                                                   
                                                                                                    

                                                                                            
                                                                       
                                                                                            
                                    
                                                                             
                                                                             
                              
                                             
                                     
                                                                                     
                   

                                                         
                                                                
                                              
                                                                                   

                                                                     
                                                                       
                                                      
                                                                                             
                                                                              

                                                                                               
                                                
                                                                                   
                                                                             
                                             
                            
                                               

                                         
                                                                       
         
                                                                       
                                    
                                                                          

end OrbitIntegral

end

end MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup
