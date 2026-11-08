/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
module
/- Modified for this distribution (2026): Lean compiler/module compatibility and
   library interface adaptations. Existing source notices are retained. -/

public import StochasticCalculus.ItoFormulaPartition

@[expose] public section

/-!
# Continuous modifications of natural Itô processes

Doob's compact-time `L²` bound for a continuous modification of a natural
Itô process, uniform-step control of differences of continuous
modifications, the limit of a fast-converging sequence of modifications,
continuous representatives of elementary finite combinations, and the
existence of a continuous modification of every natural predictable Itô
integral, with its before-stop quadratic variation.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal

noncomputable section

namespace StochasticCalculus

variable {W : Type*}  
  [MeasurableSpace W]
  {P : Measure W} {B X μ σ : ℝ≥0 → W → ℝ}

variable   
  [IsProbabilityMeasure P]

                                                                       
                                                                          
                                                                    
                                                                         
                                     
                                                                          
                                                                      
                                                           
                     
                                           
                                                         
                         
                                                                  
                                    
                        
                                                
                  
                                                          
                  
                                                                 
                                      
                                        
                                              
                        
           
                                                                       
                            
                                                                              
                
                                                                 
                                 
                                                                  
                                  
                                 
                  
                                                     
                
               
                                                    
      
                                          
                                                            
                                      
                                                                             
                    

                                                                           
                                                                        
                                                                           
                              
                                            
                                                                      
                                                             
                         
                                         
                                                          
                                         
                                                            
                                   
                                                          
                                                      
             
           
                                                                        
                                                 
                             
                         
                                                             
                        
                     

                                                                       
                                                                          
                                                
                                                                    
                                                                      
                                                             
                         
                                         
                                                          
                                         
                                                          
                         
                                     
                                                  
                                        
                                                                    
                                                                  

                                                                        
                                                                            
                                                                           
                                                         
                                                                 
                                                                      
                                                               
                         
                                                
                                                                 
                                     
                      
                                                                 
               
                                                             
                                                             
                               
                               
                                                        
                      
               
                                                                   
           
                                    
                                                          
                                    
                 
                                                                      
                                                              
                                               
                                                            
                                              
                                        
                                   
             
               
                                     

/-- Pointwise canonical limit of a sequence of candidate process
representatives.  The fallback branch is irrelevant on the almost-everywhere
set where the sequence is Cauchy. -/
noncomputable def continuousModificationSequenceLimit
    (Y : ℕ → ℝ≥0 → W → ℝ) : ℝ≥0 → W → ℝ :=
  fun s omega => completeCauchySeqLimit (fun n => Y n s omega)

                                                                        
                                                                            
                                                                        
                       
                                                                
                                                                      
                                                           
                                                               
                         
                                                
                                                                 
                                                  
                                     
                                 
                                                                 
                                                             
                                   
                                                    
                                                     
                                          
                                             
                        
           
                                   
                                     
                                                          
                                                               
                        
           
                                                                   
                                            
                                       
                                                              
                                 
                                             
           
                                                              
                                                  
                                    
                                               
                                       
              
                                             
                                                                            
             
           
                                                               
                                  
                                                          
                                                                      
                                                 
                                                
                                                                     
                                                           
             
                                          
                                                                   
                                                                   
                                                             
                                                    
                                                       
                                   
                                                                             
                    
                                                                             
                           
                                                                       
                    
                                                                       
                                        
                                                                    
                             
                                                       
                                                                    
                           
                                          
                                                                              
                    
                                                 
                                                               
                                                                                
                                                                     
                                                              
                                                     
                                        
                                                               
                                              
             
                                                                             
                                    
                                                                    
                                                    
                                                      
                                                       
                                                               
                                    
           
                                                               
                                        
                                                       
                                 
                                                
                                               
                                                            
                                           
                                                          

/-- The explicit continuous Brownian-block representative of the natural Itô
process associated with a finite elementary predictable integrand. -/
noncomputable def elementaryFinsuppItoContinuousRepresentative
    (B : ℝ≥0 → W → ℝ) (hsm : ∀ t, StronglyMeasurable (B t))
    (v : ElementaryPredictableIndex (Filtration.natural B hsm) P →₀ ℝ) :
    ℝ≥0 → W → ℝ :=
  fun s omega => ∑ x ∈ v.support,
    v x * (x.2.2 : W → ℝ) omega *
      (B (min s x.2.1.1) omega - B (min s x.1) omega)

                                                                        
                                                          
                                                  
                                                                     
                                                                        
                                   
                                                                     
                                       
                                          
                                                                    
             
           
                                                                         
                                       
                                                 
                                                                  
                                                        
                                                                              
                                    
                                                    
                                                       
                              
               
                              
                                                                   
                                                                 

                                                                          
                                                                         
                                                                   
                                                                
                                                                     
                                                           
                                     
             
                                                                       
                  
                                       
                                                      
                                          
                                                                       
                                         
                                                
                                                                          
                                                                   
                              
                                                           
                    
         
                                                               

                                                                    
                                                                    
                                                                   
                                                                        
                 
                                                       
                                                                     
                                                             
                                                      
                                                                                  
                                           
                          
                                                            
                                                        
                                                                  
                                           
                                        
                            
                                                                     
                                               
                                                        
           
                                
                                                  
                                                                            
                   
           
                                   
                                                         
                                
              
                                                             
                                
                                                                       
                                                      
                              
                                       
                           
                                 
                                                            
                 
                      
                        
                     
                              
           
                 
              
                                         
                                
           
                                                              
          
                                                     
                                 
                                                                    
                                                      
                                                                    
                     
                                     
                       
                                                                  
                                       
                                    
                                                            
        
                                                               
                                    
                                                                
                                                              
                                             
                        
                
                         
                                                             
                                     
           
                                                   
                                              
                             
        
                                              
                                                  
                                                 
                                                      
              
                   
                                       
                                               
                                                              
                                                    
                                 
                                                                     
                  
                    
                                                             
                                             
                          
               
                                                                      
               
                                    
                                   
                                     
                                 
                                                             
                                                           
                            
                
                                   
                                                                      
                             
                                              
                                                        
                              
                
                                    
                                        
                                                 
                                            
                                                                  
                                                              
                                                          
                                          
           
                                                           
                                                         
                                         
                                                               
                                               
                                                            
                                                    
                                    

                                                                         
                                                                            
                                                                          
                                     
                                                                       
                                                                     
                                                           
                              
                      
                                                  
                                                                          
                    
                                                                        
                        
                                                                    
                     
                                                            
                                                       
           
                                   
                                       
                                                         
                                                                
               
                                                                      
                  
                                                                
                           
                                                           

omit   [MeasurableSpace W]  in
/-- Along a continuous path, the second-derivative weights at a fine left
endpoint and at the left endpoint of its active coarse block become uniformly
close as both meshes vanish. -/
theorem generalItoSecondDerivative_activeBlockWeight_eventually_small
    (f : ℝ → ℝ → ℝ) (X : ℝ≥0 → W → ℝ) (t : ℝ≥0) (omega : W)
    (hsecond : Continuous (fun p : ℝ × ℝ =>
      itoSpaceSecondDerivative f p.1 p.2))
    (hpath : ContinuousOn (fun s => X s omega) (Set.Icc 0 t)) :
    ∀ epsilon : ℝ, 0 < epsilon → ∃ N : ℕ, ∀ k n, N ≤ k → N ≤ n →
        ∀ i ∈ Finset.range (n + 1), ∀ j ∈ Finset.range (k + 1),
          uniformPartitionTime t (k + 1) j <
              uniformPartitionTime t (n + 1) (i + 1) ∧
            uniformPartitionTime t (n + 1) (i + 1) ≤
              uniformPartitionTime t (k + 1) (j + 1) →
          |itoSpaceSecondDerivative f
              (uniformPartitionTime t (n + 1) i : ℝ)
              (X (uniformPartitionTime t (n + 1) i) omega) -
            itoSpaceSecondDerivative f
              (uniformPartitionTime t (k + 1) j : ℝ)
              (X (uniformPartitionTime t (k + 1) j) omega)| < epsilon := by
  let g : ℝ≥0 → ℝ := fun s =>
    itoSpaceSecondDerivative f (s : ℝ) (X s omega)
  have hpair : ContinuousOn
      (fun s : ℝ≥0 => ((s : ℝ), X s omega)) (Set.Icc 0 t) :=
    NNReal.continuous_coe.continuousOn.prodMk hpath
  have hg : ContinuousOn g (Set.Icc 0 t) := by
    exact hsecond.comp_continuousOn hpair
  have huc : UniformContinuousOn g (Set.Icc 0 t) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hg
  intro epsilon hepsilon
  obtain ⟨eta, heta, hmod⟩ :=
    Metric.uniformContinuousOn_iff.mp huc epsilon hepsilon
  have hdivNN : Filter.Tendsto
      (fun m : ℕ => t / ((m + 1 : ℕ) : ℝ≥0)) Filter.atTop (nhds 0) :=
    (Filter.tendsto_add_atTop_iff_nat 1).2
      (tendsto_const_div_atTop_nhds_zero_nat t)
  have hdiv : Filter.Tendsto
      (fun m : ℕ => ((t / ((m + 1 : ℕ) : ℝ≥0) : ℝ≥0) : ℝ))
      Filter.atTop (nhds (0 : ℝ)) := by
    change Filter.Tendsto
      (NNReal.toReal ∘ fun m : ℕ => t / ((m + 1 : ℕ) : ℝ≥0))
      Filter.atTop (nhds (0 : ℝ))
    simpa only [NNReal.coe_zero] using
      (NNReal.continuous_coe.tendsto 0).comp hdivNN
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hdiv (eta / 2) (half_pos heta)
  refine ⟨N, ?_⟩
  intro k n hkN hnN
  have hkmesh : ((t / ((k + 1 : ℕ) : ℝ≥0) : ℝ≥0) : ℝ) < eta / 2 := by
    have hnear := hN k hkN
    simpa only [Real.dist_eq, sub_zero,
      abs_of_nonneg (NNReal.coe_nonneg _)] using hnear
  have hnmesh : ((t / ((n + 1 : ℕ) : ℝ≥0) : ℝ≥0) : ℝ) < eta / 2 := by
    have hnear := hN n hnN
    simpa only [Real.dist_eq, sub_zero,
      abs_of_nonneg (NNReal.coe_nonneg _)] using hnear
  intro i hi j hj hactive
  have hnpos : 0 < n + 1 := Nat.zero_lt_succ n
  have hkpos : 0 < k + 1 := Nat.zero_lt_succ k
  have hi0 : i ≤ n + 1 :=
    (Nat.le_add_right i 1).trans (Finset.mem_range.mp hi)
  have hj0 : j ≤ k + 1 :=
    (Nat.le_add_right j 1).trans (Finset.mem_range.mp hj)
  have hifine := uniformPartitionTime_mem_Icc_of_le t hnpos hi0
  have hjcoarse := uniformPartitionTime_mem_Icc_of_le t hkpos hj0
  have hdistLe := dist_uniformPartition_left_to_active_coarse_left_le
    t (n + 1) (k + 1) i j hnpos hkpos hactive
  have hdist : dist (uniformPartitionTime t (n + 1) i)
      (uniformPartitionTime t (k + 1) j) < eta := by
    calc
      _ ≤ ((t / ((n + 1 : ℕ) : ℝ≥0) : ℝ≥0) : ℝ) +
          ((t / ((k + 1 : ℕ) : ℝ≥0) : ℝ≥0) : ℝ) := hdistLe
      _ < eta / 2 + eta / 2 := add_lt_add hnmesh hkmesh
      _ = eta := by ring
  have hout := hmod
    (uniformPartitionTime t (n + 1) i) hifine
    (uniformPartitionTime t (k + 1) j) hjcoarse hdist
  simpa only [g, Real.dist_eq] using hout

end StochasticCalculus
