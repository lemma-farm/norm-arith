/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Topology.Compactness.SigmaCompact
import Mathlib.Topology.Metrizable.Urysohn
import MarkovProcess.Kernel.PositiveC0Resolvent
import MarkovProcess.Semigroup.ResolventGeneration

/-!
# One-point extension of a positive `C₀` resolvent

A positive contractive resolvent on a locally compact Polish space generates a sub-Markov
semigroup. This file adjoins the genuine Alexandroff point at infinity, extends continuous
functions by splitting off their value there, and lets the generated semigroup evolve only the
part which vanishes at infinity. The resulting positive contractive resolvent has a conservative
Feller kernel semigroup, and the added point is absorbing.

Main results: `PositiveC0ContractiveResolvent.onePointResolvent`,
`PositiveC0ContractiveResolvent.onePointResolvent_operator`,
`PositiveC0ContractiveResolvent.isConservative_onePointKernelSemigroup`, and
`PositiveC0ContractiveResolvent.onePointKernelSemigroup_absorbing`.

This construction does not assert a Kolmogorov moment bound or construct a continuous-path
process.
-/

open Filter Set Topology TopologicalSpace

noncomputable section

namespace OnePoint

variable {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [SecondCountableTopology X]

private def basis : Set (Set (OnePoint X)) :=
  ((fun s : Set X => ((↑) '' s : Set (OnePoint X))) '' TopologicalSpace.countableBasis X) ∪
    Set.range (fun n : ℕ => OnePoint.opensOfCompl
      (CompactExhaustion.choice X n)
      ((CompactExhaustion.choice X).isCompact n).isClosed
      ((CompactExhaustion.choice X).isCompact n))

private theorem basis_countable : (basis (X := X)).Countable := by
  apply Set.Countable.union
  · exact (TopologicalSpace.countable_countableBasis X).image _
  · exact Set.countable_range _

private theorem basis_isOpen (s : Set (OnePoint X)) (hs : s ∈ basis (X := X)) : IsOpen s := by
  rcases hs with hs | hs
  · rcases hs with ⟨u, hu, rfl⟩
    exact OnePoint.isOpen_image_coe.mpr
      ((TopologicalSpace.isBasis_countableBasis X).isOpen hu)
  · rcases hs with ⟨n, rfl⟩
    exact (OnePoint.opensOfCompl (CompactExhaustion.choice X n)
      ((CompactExhaustion.choice X).isCompact n).isClosed
      ((CompactExhaustion.choice X).isCompact n)).is_open'

private theorem basis_isTopologicalBasis : IsTopologicalBasis (basis (X := X)) := by
  apply isTopologicalBasis_of_isOpen_of_nhds basis_isOpen
  intro z u hzu hu
  induction z using OnePoint.rec with
  | infty =>
    have hu_inf : OnePoint.infty ∈ u := hzu
    rw [OnePoint.isOpen_iff_of_mem hu_inf] at hu
    obtain ⟨n, hn⟩ := (CompactExhaustion.choice X).exists_superset_of_isCompact hu.2
    refine ⟨OnePoint.opensOfCompl (CompactExhaustion.choice X n)
      ((CompactExhaustion.choice X).isCompact n).isClosed
      ((CompactExhaustion.choice X).isCompact n), ?_, ?_, ?_⟩
    · exact Or.inr ⟨n, rfl⟩
    · exact OnePoint.infty_mem_opensOfCompl _ _
    · intro z hz
      induction z using OnePoint.rec with
      | infty => exact hu_inf
      | coe x =>
        change (x : OnePoint X) ∈
          (((↑) '' (CompactExhaustion.choice X n)) : Set (OnePoint X))ᶜ at hz
        have hx : x ∈ ((CompactExhaustion.choice X n) : Set X)ᶜ := by
          simpa only [Set.mem_compl_iff, Set.mem_image, OnePoint.coe_eq_coe,
            exists_eq_right] using hz
        have hxpre : x ∈ ((↑) ⁻¹' u : Set X) := by
          by_contra hxnot
          exact hx (hn hxnot)
        exact hxpre
  | coe x =>
    have hx : x ∈ ((↑) ⁻¹' u : Set X) := hzu
    have hopen : IsOpen (((↑) ⁻¹' u : Set X)) :=
      OnePoint.continuous_coe.isOpen_preimage _ hu
    obtain ⟨v, hvbasis, hxv, hvu⟩ :=
      (TopologicalSpace.isBasis_countableBasis X).exists_subset_of_mem_open hx hopen
    refine ⟨((↑) '' v : Set (OnePoint X)), ?_, ⟨x, hxv, rfl⟩, ?_⟩
    · exact Or.inl ⟨v, hvbasis, rfl⟩
    · rintro _ ⟨y, hyv, rfl⟩
      exact hvu hyv

/-- The one-point compactification of a second-countable locally compact Hausdorff space is
second countable. -/
noncomputable instance instSecondCountableTopology : SecondCountableTopology (OnePoint X) :=
  (basis_isTopologicalBasis (X := X)).secondCountableTopology (basis_countable (X := X))

/-- The canonical measurable structure on a one-point compactification is its Borel structure. -/
instance instMeasurableSpace : MeasurableSpace (OnePoint X) :=
  borel (OnePoint X)

/-- The canonical measurable structure on a one-point compactification is Borel. -/
instance instBorelSpace : BorelSpace (OnePoint X) :=
  ⟨rfl⟩

end OnePoint

namespace MarkovProcess.PositiveC0ContractiveResolvent

open MeasureTheory ProbabilityTheory
open scoped BoundedContinuousFunction NNReal ZeroAtInfty

variable {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [SecondCountableTopology X]

/-- The part of a function on the one-point compactification which vanishes at infinity. -/
noncomputable def onePointRemainder (g : C₀(OnePoint X, ℝ)) : C₀(X, ℝ) where
  toFun x := g (x : OnePoint X) - g OnePoint.infty
  continuous_toFun :=
    (g.continuous.comp OnePoint.continuous_coe).sub continuous_const
  zero_at_infty' := by
    have hg := (OnePoint.continuous_iff (g : OnePoint X → ℝ)).mp g.continuous
    rw [← Filter.coclosedCompact_eq_cocompact]
    simpa only [Function.comp_apply, sub_self] using hg.1.sub_const (g OnePoint.infty)

/-- Reassemble a vanishing function and its value at infinity. -/
noncomputable def onePointAssemble (f : C₀(X, ℝ)) (c : ℝ) : C₀(OnePoint X, ℝ) :=
  ZeroAtInftyContinuousMap.ContinuousMap.liftZeroAtInfty
    (OnePoint.continuousMapMk (f.toContinuousMap + ContinuousMap.const X c) c (by
      rw [Filter.coclosedCompact_eq_cocompact]
      simpa only [ContinuousMap.coe_add, ContinuousMap.coe_const, Pi.add_apply, zero_add]
        using! (zero_at_infty f).add_const c))

                                                           
                                                            
                                                                         
                                                                        

omit [LocallyCompactSpace X] [SecondCountableTopology X] in
/-- The assembled observable at a live point. -/
@[simp] theorem onePointAssemble_coe (f : C₀(X, ℝ)) (c : ℝ) (x : X) :
    onePointAssemble f c (x : OnePoint X) = f x + c := by
  rfl

omit [LocallyCompactSpace X] [SecondCountableTopology X] in
/-- The assembled observable at the added point. -/
@[simp] theorem onePointAssemble_infty (f : C₀(X, ℝ)) (c : ℝ) :
    onePointAssemble f c OnePoint.infty = c := by
  rfl

                                                           
                                                                    
                                                                   
                                                      
                                    
         
                                                                                   
                         

                                                           
                                                                                             
                                                                    
                                                                       
                                    
         
                                     
                
                                                                                      

                                                           
                                 
                                                                 
                                                                               
                                    
         
                                                                         
      

                                                           
                                                         
                                                                        
                                                             
                                    
         
                                                                                       
      

                                                      
                                          
                            
                                   
                                     

omit [LocallyCompactSpace X] [SecondCountableTopology X] in
private theorem norm_onePointRemainder_le (g : C₀(OnePoint X, ℝ)) :
    ‖onePointRemainder g‖ ≤ 2 * ‖g‖ := by
  rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
  refine (BoundedContinuousFunction.norm_le (mul_nonneg (by norm_num) (norm_nonneg g))).2 fun x ↦ ?_
  change ‖g (x : OnePoint X) - g OnePoint.infty‖ ≤ 2 * ‖g‖
  calc
    ‖g (x : OnePoint X) - g OnePoint.infty‖ ≤
        ‖g (x : OnePoint X)‖ + ‖g OnePoint.infty‖ := norm_sub_le _ _
    _ ≤ ‖g‖ + ‖g‖ := add_le_add
      (g.toBCF.norm_coe_le_norm (x : OnePoint X))
      (g.toBCF.norm_coe_le_norm OnePoint.infty)
    _ = 2 * ‖g‖ := by ring

                                                
                                       
                                                                     

                                                           
                                                                            
                                                       

variable [MeasurableSpace X] [BorelSpace X]

variable (R : PositiveC0ContractiveResolvent X)

/-- Extend the generated semigroup action by fixing the value at infinity. -/
noncomputable def onePointSemigroupAction (t : NNReal) (g : C₀(OnePoint X, ℝ)) :
    C₀(OnePoint X, ℝ) :=
  onePointAssemble
    (R.toContractiveResolvent.generatedSemigroup t (onePointRemainder g))
    (g OnePoint.infty)

omit [MeasurableSpace X] [BorelSpace X] [LocallyCompactSpace X] [SecondCountableTopology X] in
/-- The extended action fixes the value of an observable at the added point. -/
@[simp] theorem onePointSemigroupAction_infty (t : NNReal) (g : C₀(OnePoint X, ℝ)) :
    R.onePointSemigroupAction t g OnePoint.infty = g OnePoint.infty := by
  rw [onePointSemigroupAction, onePointAssemble_infty]

/-- At a live point, the extended semigroup integrates over the original transition law and
assigns its missing mass to the value of the observable at infinity. -/
theorem onePointSemigroupAction_coe (t : NNReal) (g : C₀(OnePoint X, ℝ)) (x : X) :
    R.onePointSemigroupAction t g (x : OnePoint X) =
      ∫ y, g (y : OnePoint X) ∂R.kernelSemigroup t x +
        (1 - (R.kernelSemigroup t x).real Set.univ) * g OnePoint.infty := by
  rw [onePointSemigroupAction, onePointAssemble_coe,
    ← R.integral_kernelSemigroup t (onePointRemainder g) x]
  let μ := R.kernelSemigroup t x
  have hmassE := R.kernelSemigroup.measure_univ_le_one t x
  have hfin : μ Set.univ < ⊤ :=
    lt_of_le_of_lt hmassE ENNReal.one_lt_top
  let : IsFiniteMeasure μ := ⟨hfin⟩
  let gc : X →ᵇ ℝ := g.toBCF.compContinuous
    ⟨fun x : X ↦ (x : OnePoint X), OnePoint.continuous_coe⟩
  have hg : Integrable (fun y : X ↦ g (y : OnePoint X)) μ := gc.integrable μ
  rw [show (∫ y, onePointRemainder g y ∂μ) =
      ∫ y, (g (y : OnePoint X) - g OnePoint.infty) ∂μ by rfl,
    integral_sub hg (integrable_const _), integral_const]
  change (∫ y, g (y : OnePoint X) ∂μ) - μ.real Set.univ * g OnePoint.infty +
      g OnePoint.infty = _
  ring

private theorem norm_onePointSemigroupAction_le (t : NNReal) (g : C₀(OnePoint X, ℝ)) :
    ‖R.onePointSemigroupAction t g‖ ≤ ‖g‖ := by
  rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
  refine (BoundedContinuousFunction.norm_le (norm_nonneg g)).2 fun z ↦ ?_
  induction z using OnePoint.rec with
  | infty =>
      change ‖R.onePointSemigroupAction t g OnePoint.infty‖ ≤ ‖g‖
      rw [onePointSemigroupAction_infty]
      exact g.toBCF.norm_coe_le_norm OnePoint.infty
  | coe x =>
      change ‖R.onePointSemigroupAction t g (x : OnePoint X)‖ ≤ ‖g‖
      rw [Real.norm_eq_abs, onePointSemigroupAction_coe]
      let μ := R.kernelSemigroup t x
      have hmassE : μ Set.univ ≤ 1 := R.kernelSemigroup.measure_univ_le_one t x
      have hfin : μ Set.univ < ⊤ := lt_of_le_of_lt hmassE ENNReal.one_lt_top
      let : IsFiniteMeasure μ := ⟨hfin⟩
      have hmass0 : 0 ≤ μ.real Set.univ := measureReal_nonneg
      have hmass1 : μ.real Set.univ ≤ 1 := by
        rw [measureReal_def]
        simpa only [ENNReal.toReal_one] using
          (ENNReal.toReal_le_toReal hfin.ne ENNReal.one_ne_top).mpr hmassE
      have hint : |∫ y, g (y : OnePoint X) ∂μ| ≤ ‖g‖ * μ.real Set.univ := by
        rw [← Real.norm_eq_abs]
        exact norm_integral_le_of_norm_le_const
          (ae_of_all μ fun y ↦ g.toBCF.norm_coe_le_norm (y : OnePoint X))
      calc
        |∫ y, g (y : OnePoint X) ∂μ +
            (1 - μ.real Set.univ) * g OnePoint.infty| ≤
            |∫ y, g (y : OnePoint X) ∂μ| +
              |(1 - μ.real Set.univ) * g OnePoint.infty| := abs_add_le _ _
        _ ≤ ‖g‖ * μ.real Set.univ +
              (1 - μ.real Set.univ) * ‖g‖ := by
          refine add_le_add hint ?_
          rw [abs_mul, abs_of_nonneg (sub_nonneg.mpr hmass1)]
          exact mul_le_mul_of_nonneg_left
            (g.toBCF.norm_coe_le_norm OnePoint.infty) (sub_nonneg.mpr hmass1)
        _ = ‖g‖ := by ring

                                                                   
                                                   
                                      
                    
                                      
           
                                       
                                                                                            
              
                                                                                      
                                                    
          
                     
                                      
           
                                       
                                                                                             
                         
              
                                                                                       
                                                                                     
          

                                                                              
                                                          
                                                
                                                            
                                                                     

                                                                           
                                                                                      
                                                                          

                                                                                         
                                       
                    
                                      
           
                                       
                                                                                               
                                                                                             
                     
                                      
           
                                       
                                                                                      
                                    
                                                                                    
                                                

                                                                                              
                                                      
                                      
                                                    
                                                                         
                                     
            
                                                        
                                            
                         
            
                                                          
                                         
                                      

                                                                             
                                                  
                                                       

                                                                                              
                                                            
                                                 

                                                                                              
                                                                                 
                                   
                                                                                           
                                                   
                                    
         
                                     
            
                                                                    
                                                                             
            
                                                               
                                                                
                                            
          

                                                                 
                                     
                                                                            
                                         
                     
                                 
           
                                                                 
                                                             
                                 
       
                        
                                 
           
                                                
                                                                 
                                                         
                                                          
                                                            
       
                       
                                                           
           
                                                 
                                               
                          
                                                                
                                                                                             
                                                  
              
                                                                       
                                        
                                                                                         
                        

                                                                        
                                                                              
                                                                  

                                                                            
                                                   
                                                                      
              
                                     
            
                                                                 
                             
            
                                                               
                      
                                                         
                        
                                                                  
                                                             
                                                         
                                          
                                               
                                                                         
                                 

                                                               
                                
                        
                          
                               
                                  
                
                  
                                      

                                                                                     
                                                                                 
              
                                                   
                                                                 
                                 
                                                                         
                                                 
                                                                      
                             
                       
                                       
                                             
                                                                                

                                                                                    
                                                                                       
                                                                      
                                                      

                                                                                           
                                              
                                                                                          
                                                               

                                                                          
                             
                                                                                  
                                                                      
                                                                   
                                                                 
                             
                                                                               
                                               
                                                                      
                                                                 
                                                      
                                                      
                           
                                                                     
                               
                                       
                       
                                                                                     
                                                                  
                                                        

                                                                      
                             
                                                                             
                                         
                                                              
                                                                 
                                          
                                                                               
                                                              
                                                                      
                                 
                                                      
                         
                                                                                               

                                                                                                
                
                                                                 
                             
                                                              
                      
                                                                    
                                             
                                                                             
                                           

                                                                             
                                                                                    
                                     

                                                               
                                                         
                                                        
                                                             

                                                                                      
             
                                                                             
                      
                                                                             
                                                                            
                                           

                                                                         
                      

                                                                                              
                                                                         
                                  
                                     
                                             
                                                               
                                                    

                                                      
                                                                 
                                                                         
                                                                         
                               
                                              

                                                              
                                                
                                                  
           
                                                                       
                                        
                                                                               
                                                      
         

                                                                                              
                                                        
                                                                                   
                                                                              
                                                    
                                          
                                                        
         
                               
                                                               
                                                                  
                                                                  
                                                                                       
                                      


end MarkovProcess.PositiveC0ContractiveResolvent
