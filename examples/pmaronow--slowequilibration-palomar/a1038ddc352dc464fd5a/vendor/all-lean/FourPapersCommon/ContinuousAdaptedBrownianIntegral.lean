module

public import FourPapersCommon.ContinuousAdaptedPredictable
public import StochasticCalculus.MartingaleLeftSum
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

public section

/-! Bounded continuous adapted coefficients integrate against the genuine
Brownian motion. Their uniform left sums converge to that constructed Itô
integral, with no stochastic representation premise. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter StochasticCalculus
open scoped NNReal ENNReal Topology BigOperators
namespace FourPapersCommon
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
set_option maxHeartbeats 1000000

@[expose] def boundedAdaptedCoefficient (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (H : ℝ≥0 → Ω → ℝ) (hH : StronglyAdapted 𝓕 H) (K : ℝ≥0)
    (hK : ∀ t ω, ‖H t ω‖ ≤ K) (t : ℝ≥0) : lpMeas ℝ ℝ (𝓕 t) 2 P :=
  let hm : MemLp (H t) 2 P := MemLp.of_bound
    ((hH t).mono (𝓕.le t)).aestronglyMeasurable K (.of_forall (hK t))
  ⟨hm.toLp (H t), (hH t).aestronglyMeasurable.congr hm.coeFn_toLp.symm⟩

theorem boundedAdaptedCoefficient_coeFn (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (H : ℝ≥0 → Ω → ℝ) (hH : StronglyAdapted 𝓕 H) (K : ℝ≥0)
    (hK : ∀ t ω, ‖H t ω‖ ≤ K) (t : ℝ≥0) :
      (boundedAdaptedCoefficient (P:=P) 𝓕 H hH K hK t : Ω → ℝ) =ᵐ[P] H t := by
  unfold boundedAdaptedCoefficient
  exact (MemLp.of_bound ((hH t).mono (𝓕.le t)).aestronglyMeasurable
    K (.of_forall (hK t)) : MemLp (H t) 2 P).coeFn_toLp

theorem elementaryPredictable_boundedCoefficient_coeFn
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (H : ℝ≥0 → Ω → ℝ) (hH : StronglyAdapted 𝓕 H) (K : ℝ≥0)
    (hK : ∀ t ω, ‖H t ω‖ ≤ K) (a b : ℝ≥0) :
    (elementaryPredictable 𝓕 a b (boundedAdaptedCoefficient (P:=P) 𝓕 H hH K hK a) :
      ℝ≥0 × Ω → ℝ) =ᵐ[nonnegativeLebesgueMeasure.prod P]
      elementaryRepresentative 𝓕 a b (H a) := by
  have hz : (fun p : ℝ≥0 × Ω =>
      (boundedAdaptedCoefficient (P:=P) 𝓕 H hH K hK a : Ω → ℝ) p.2) =ᵐ[nonnegativeLebesgueMeasure.prod P]
      fun p => H a p.2 :=
    Measure.quasiMeasurePreserving_snd.ae_eq_comp
      (boundedAdaptedCoefficient_coeFn 𝓕 H hH K hK a)
  filter_upwards [elementaryPredictable_coeFn 𝓕 a b
    (boundedAdaptedCoefficient (P:=P) 𝓕 H hH K hK a), hz] with p hp hz
  rw [hp]
  unfold elementaryRepresentative
  rw [hz]

                                            
                                            
                                                          
                                                 
                                                          
                                                       
                                                                             
                                                                                             
           
                   
              
                                                                  
                                                                         
                                                                                                      
                                                                             
                                                                 
                                                                                    
                                                                  
                                                                         
                                                                                
                                                                                    
                                                                       
                               
                                                                                                                   
                                                                     
                                                                                    
             
                                                                        

                                                                 
                                                                      
                                                                                  
                                                
                                                       
                                                       
                                                                                  

                                                   
                                                                                        
                                                                                  
                                                          
                                                 
                                   
                                                                           
                                                                
           
                                                                        
                                                             
                                                                                   
                                                
                                           
                                                                                             
                                                             
                                                               
                                                                                      
                                                                                          
                  
               
                                           
                                                                                                  
                                                      
                              
             
                                                                  
          
                                                                         
                                                                             
                                                          
                                        

                                                         
                                                                                        
                                                                                  
                                                
                                                       
                                         
                                                                                      
                                                                                      
                                                                                  
                                                                     
                                   
                                                                                          
                                       

end FourPapersCommon
