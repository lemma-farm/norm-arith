module

public import SphericalAging.LocalSDE
public import Mathlib.Analysis.SpecialFunctions.Exp

public section

/-! The bounded invertible exponential multiplier on the actual closed
predictable product L² space. It supplies a complete Banach space for Picard
on every finite horizon without changing the driving filtration. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal
namespace SphericalAging.WeightedPredictable
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

@[expose] abbrev PredictableL2 (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (P : Measure Ω) :=
  lpMeas E ℝ F.predictable 2 (nonnegativeLebesgueMeasure.prod P)

theorem time_stronglyMeasurable (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) :
    StronglyMeasurable[F.predictable] (fun q : ℝ≥0 × Ω => q.1) := by
  apply Measurable.stronglyMeasurable
  apply measurable_of_Ioi
  intro t
  convert (measurableSet_predictable_Ioi_prod (𝓕 := F) (i := t)
    (show MeasurableSet[F t] (univ : Set Ω) from MeasurableSet.univ)) using 1
  ext q
  simp

@[expose] def weight (α : ℝ) (T t : ℝ≥0) : ℝ := Real.exp (-α * (min t T : ℝ≥0))

theorem weight_pos (α : ℝ) (T t : ℝ≥0) : 0 < weight α T t := Real.exp_pos _

theorem weight_continuous (α : ℝ) (T : ℝ≥0) : Continuous (weight α T) := by
  unfold weight
  fun_prop

theorem weight_stronglyMeasurable (α : ℝ) (T : ℝ≥0) :
    StronglyMeasurable[F.predictable] (fun q : ℝ≥0 × Ω => weight α T q.1) :=
  (weight_continuous α T).comp_stronglyMeasurable (time_stronglyMeasurable F)

theorem weight_le (α : ℝ) (T t : ℝ≥0) : weight α T t ≤ Real.exp (|α| * T) := by
  apply Real.exp_le_exp.mpr
  exact (mul_le_mul_of_nonneg_right (neg_le_abs α) (min t T).coe_nonneg).trans
    (mul_le_mul_of_nonneg_left (show (min t T : ℝ≥0) ≤ T from min_le_right _ _) (abs_nonneg _))

                                                                                         
                                     
                                                                         
                         

theorem weighted_memLp (α : ℝ) (T : ℝ≥0) (U : PredictableL2 E F P) :
    MemLp (fun q => weight α T q.1 • (U : Lp E 2 (nonnegativeLebesgueMeasure.prod P)) q)
      2 (nonnegativeLebesgueMeasure.prod P) := by
  apply (Lp.memLp (U : Lp E 2 (nonnegativeLebesgueMeasure.prod P))).of_le_mul (c := Real.exp (|α| * T))
    (((weight_stronglyMeasurable (F := F) α T).aestronglyMeasurable.smul
      (lpMeas.aestronglyMeasurable U)).mono (predictable_le_prod F))
  exact .of_forall (fun q => by
    change ‖weight α T q.1 • (U : Lp E 2 (nonnegativeLebesgueMeasure.prod P)) q‖ ≤
      Real.exp (|α| * T) * ‖(U : Lp E 2 (nonnegativeLebesgueMeasure.prod P)) q‖
    rw [norm_smul, Real.norm_of_nonneg (weight_pos α T q.1).le]
    exact mul_le_mul_of_nonneg_right (weight_le α T q.1) (norm_nonneg _))

@[expose] def multiply (α : ℝ) (T : ℝ≥0) (U : PredictableL2 E F P) : PredictableL2 E F P :=
  ⟨(weighted_memLp α T U).toLp _,
    ((weight_stronglyMeasurable (F := F) α T).aestronglyMeasurable.smul
      (lpMeas.aestronglyMeasurable U)).congr (weighted_memLp α T U).coeFn_toLp.symm⟩

theorem multiply_coeFn (α : ℝ) (T : ℝ≥0) (U : PredictableL2 E F P) :
    (multiply α T U : Lp E 2 (nonnegativeLebesgueMeasure.prod P))
      =ᵐ[nonnegativeLebesgueMeasure.prod P]
      (fun q => weight α T q.1 • (U : Lp E 2 (nonnegativeLebesgueMeasure.prod P)) q) :=
  (weighted_memLp α T U).coeFn_toLp

theorem norm_multiply_le (α : ℝ) (T : ℝ≥0) (U : PredictableL2 E F P) :
    ‖multiply α T U‖ ≤ Real.exp (|α| * T) * ‖U‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [multiply_coeFn α T U] with q hq
  change ‖(multiply α T U : Lp E 2 (nonnegativeLebesgueMeasure.prod P)) q‖ ≤
    Real.exp (|α| * T) * ‖(U : Lp E 2 (nonnegativeLebesgueMeasure.prod P)) q‖
  rw [hq, norm_smul, Real.norm_of_nonneg (weight_pos α T q.1).le]
  exact mul_le_mul_of_nonneg_right (weight_le α T q.1) (norm_nonneg _)

                                                                    
                                                                
                   
              
                                                                                       
                                                                    
                                                                                                
                              
                                                                                           

                                                                    
                                                                
                   
              
                                                                                       
                                                                    
                                                                                                
                              
                                                                                           

                                                                                             
                                                           
                               

                                                                           
                                                   
                   
              
                                                                   
                                                                     
                                                                                  
                          
                                                                         
                                                

                                                                 
                                                                                                   
           
                                            
                                 
                                                    

section StateCoefficients
                                          
                                         

                                                            
                                    
                                                                                                   
                   
              
                                                                                          
                                                
                                                                                              
                                                                

                                        
                                                                          
                                      
                                                                                    
                                          
                                        
                                                                                                     
                                                                                                       
                                                                                                   
                                                                            
                                                     
                                                                                         
                                     
                                                                                 
                        
                                                                           
                              
                                                                                     
                                                                                 
                                                                         
                                                                               
                                                                        
                        
                                                                      
                                                              
                                                 
end StateCoefficients

                                                                      
                                              
                   
              
                                                                                               
                                                             

                                                                      
                                              
                                                      

                                              
                                                                      
             
                                         
                                        

end SphericalAging.WeightedPredictable
