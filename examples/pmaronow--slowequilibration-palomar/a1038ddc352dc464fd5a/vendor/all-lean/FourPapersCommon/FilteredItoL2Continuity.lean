module

public import FourPapersCommon.FilteredItoProcess
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Topology.Sequences

public section

/-! Mean-square continuity of the actual full-filtration Ito process.
This extends the terminal isometry to a continuous `L²(P)`-valued process,
without assuming pathwise continuity or identifying the filtration with a
single Brownian coordinate's natural filtration. -/

noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal InnerProductSpace

namespace FourPapersCommon.FilteredBrownian

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

theorem nonnegativeLebesgueMeasure_singleton (t : ℝ≥0) :
    nonnegativeLebesgueMeasure ({t} : Set ℝ≥0) = 0 := by
  rw [nonnegativeLebesgueMeasure, measurableEmbedding_nnrealCoe_iterated.comap_apply]
  simp

theorem ae_time_ne (t : ℝ≥0) :
    ∀ᵐ p : ℝ≥0 × Ω ∂nonnegativeLebesgueMeasure.prod P, p.1 ≠ t := by
  rw [ae_iff]
  have hset : {p : ℝ≥0 × Ω | ¬p.1 ≠ t} = ({t} : Set ℝ≥0) ×ˢ univ := by
    ext p
    simp
  rw [hset, Measure.prod_prod, nonnegativeLebesgueMeasure_singleton, zero_mul]

@[expose] def timeCutRepresentative (U : PredictableProcessL2 𝓕 P) (t : ℝ≥0) :
    ℝ≥0 × Ω → ℝ := (predictableTimeFrame (W := Ω) t).indicator U

                                                                          
                 
                                                                         
                                                                          
                                                
                                   
                
                                                        
                                                        
                                                        
                                                            
                   
                         
                              
                                                     
                                                      
                                        
                                                        
                                                             
                                              

theorem timeCutRepresentative_sub_sq_le (U : PredictableProcessL2 𝓕 P)
    (s t : ℝ≥0) (p : ℝ≥0 × Ω) :
    ‖(timeCutRepresentative U s p - timeCutRepresentative U t p) ^ 2‖ ≤
      ((U : ℝ≥0 × Ω → ℝ) p) ^ 2 := by
  classical
  simp only [timeCutRepresentative, predictableTimeFrame]
  by_cases hs : p ∈ Ioc 0 s ×ˢ (univ : Set Ω)
  <;> by_cases ht : p ∈ Ioc 0 t ×ˢ (univ : Set Ω)
  <;> simp [hs, ht, Real.norm_of_nonneg (sq_nonneg _), sq_nonneg]

theorem timeCutRepresentative_tendsto (U : PredictableProcessL2 𝓕 P)
    {u : ℕ → ℝ≥0} {t : ℝ≥0} (hu : Tendsto u atTop (𝓝 t))
    (p : ℝ≥0 × Ω) (hp : p.1 ≠ t) :
    Tendsto (fun n => timeCutRepresentative U (u n) p) atTop
      (𝓝 (timeCutRepresentative U t p)) := by
  classical
  by_cases hp0 : p.1 = 0
  · have hzero : ∀ s, timeCutRepresentative U s p = 0 := by
      intro s
      simp [timeCutRepresentative, predictableTimeFrame, hp0]
    simp only [hzero]
    exact tendsto_const_nhds
  · have hp0' : 0 < p.1 := lt_of_le_of_ne (zero_le : 0 ≤ p.1) (Ne.symm hp0)
    rcases lt_or_gt_of_ne hp with hpt | htp
    · have hev : ∀ᶠ n in atTop, p.1 < u n :=
        hu.eventually (eventually_gt_nhds hpt)
      have heq : ∀ᶠ n in atTop,
          timeCutRepresentative U (u n) p = timeCutRepresentative U t p := by
        filter_upwards [hev] with n hn
        simp [timeCutRepresentative, predictableTimeFrame, hp0', hpt.le, hn.le]
      exact tendsto_const_nhds.congr' (Filter.EventuallyEq.symm heq)
    · have hev : ∀ᶠ n in atTop, u n < p.1 :=
        hu.eventually (eventually_lt_nhds htp)
      have heq : ∀ᶠ n in atTop,
          timeCutRepresentative U (u n) p = timeCutRepresentative U t p := by
        filter_upwards [hev] with n hn
        simp [timeCutRepresentative, predictableTimeFrame, not_le_of_gt htp,
          not_le_of_gt hn]
      exact tendsto_const_nhds.congr' (Filter.EventuallyEq.symm heq)

                                                                           
                                                                   
                                        
              
                                        
                                       
                                                                           
                                                      
                                                                    
                                                                          
                                                      
                                                                    
                                                                                       
                                      
                                                    
                                           
                      
                                                                     
       
                                                      
                                                                      
                                             
                                                                 
                                                    
                                                                       
                                             

                                                      
                                                                      
                                                                              
                                                        
                                                       
                                          

@[expose] def finiteTimeMeasure (T : ℝ≥0) : Measure ℝ≥0 :=
  nonnegativeLebesgueMeasure.restrict (Ioc 0 T)

instance finiteTimeMeasure_isFinite (T : ℝ≥0) : IsFiniteMeasure (finiteTimeMeasure T) :=
  isFiniteMeasure_restrict.mpr (nonnegativeLebesgueMeasure_Ioc_ne_top 0 T)

                                                      
                                                                      
                                                                            
                                                                                       
                                                                                       
                                                                   

                                                                            
                                                                           
                                                               
                                                                      
                                                                            
               
                                                                            
                             
                                                                
                                                                                 
      
                                                                            
                                                
                                                    
                                                                              
                                                         
                               
                                                                
                                                                                 

@[expose] abbrev RandomTimeL2 (P : Measure Ω) (T : ℝ≥0) :=
  Lp (RandomL2 P) 2 (finiteTimeMeasure T)

                                                
                                                                      
                                                       
                                                        
                                                            

                                                  
                                                                      
                                                       
                                    
                                                 
                                                                                  
                                                 
                         
                                                                                 
             
                                                              

                                                  
                                                                      
                                                       
                                    
                                                                     
                                                                                       
                                                                   
                                                                  

                                                                        
                                                                            
                                                       
                                                                      
                                                         
                                                         
                                              
                    
                
                                                                                         
                                                                     
                                                                     
                                                          
                                                                      
             
                                                                              
                           
                                                                                         
                                                                                       
                    
                                                                       
                     
                
                                                                                         
                                                                     
                                                                                  
                                
              
                                                                              
                           
                                                                                           
                
                                                                         

                                                 
                                                                      
                                                         
                                                      
                                                                         
                                                 

                                                 
                                                                      
                                                       
                                    
                                                                                         

                                                   
                                                                      
                                                         
                                                           
                                                                   
                          

end FourPapersCommon.FilteredBrownian
