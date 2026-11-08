module

public import GinibrePoincare.Concrete.SmoothTarget
public import GinibrePoincare.Analysis.GinibreMassFiniteness
public import Mathlib
public import Mathlib.Analysis.Convex.Integral

@[expose] public section

/-! # Actual square entropy for the radial log-Sobolev problem
These are entropy and integrability results, not a log-Sobolev inequality.
-/
open MeasureTheory
open scoped ContDiff
namespace GinibrePoincare
noncomputable section

/-- Square entropy with its actual integral definition. -/
def squareEntropy {α : Type*} [MeasurableSpace α] (μ : Measure α) (f : α → ℝ) : ℝ :=
  (∫ x, f x ^ 2 * Real.log (f x ^ 2) ∂μ) -
    (∫ x, f x ^ 2 ∂μ) * Real.log (∫ x, f x ^ 2 ∂μ)

                                                                            
                                                                 
                                    

                                                              
                                                                            
                                                     
                                                          
                                               
                                                      
                  
                    
            
                
                                                     

                                                                                
theorem continuous_square_mul_log {α : Type*} [TopologicalSpace α] {f : α → ℝ}
    (hf : Continuous f) : Continuous (fun x => f x ^ 2 * Real.log (f x ^ 2)) :=
  Real.continuous_mul_log.comp (hf.pow 2)

/-- The logarithmic entropy integrand has the same compact-support bound as `f`. -/
theorem compactSupport_square_mul_log {α : Type*} [TopologicalSpace α] {f : α → ℝ}
    (hf : HasCompactSupport f) : HasCompactSupport (fun x => f x ^ 2 * Real.log (f x ^ 2)) := by
  apply hf.mono
  intro x hx hzero
  apply hx
  simp [hzero]

                                                                           
                                                                                        
                                                     
                                                                               
                                               
                                                                      
                                       

/-- Jensen's inequality makes square entropy nonnegative for a probability law. -/
theorem squareEntropy_nonneg {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] (f : α → ℝ) (hf : Integrable (fun x => f x ^ 2) μ)
    (hlog : Integrable (fun x => f x ^ 2 * Real.log (f x ^ 2)) μ) :
    0 ≤ squareEntropy μ f := by
  have hj := Real.convexOn_mul_log.map_integral_le
    Real.continuous_mul_log.continuousOn isClosed_Ici
    (Filter.Eventually.of_forall (fun x => sq_nonneg (f x))) hf hlog
  exact sub_nonneg.mpr hj

                                                                          
                                                                                  
                                                                                        
                                               
                                                                  
                                                 

                                                      
theorem squareEntropy_map {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (T : α → β) (hT : AEMeasurable T μ) (f : β → ℝ)
    (hsq : AEStronglyMeasurable (fun y => f y ^ 2) (μ.map T))
    (hlog : AEStronglyMeasurable (fun y => f y ^ 2 * Real.log (f y ^ 2)) (μ.map T)) :
    squareEntropy (μ.map T) f = squareEntropy μ (fun x => f (T x)) := by
  unfold squareEntropy
  rw [integral_map hT hsq, integral_map hT hlog]

/-- Equal square and logarithmic moments give equal entropy (the Kostlan transfer step). -/
theorem squareEntropy_eq_of_moments {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) (f : α → ℝ) (g : β → ℝ)
    (hsq : (∫ x, f x ^ 2 ∂μ) = ∫ y, g y ^ 2 ∂ν)
    (hlog : (∫ x, f x ^ 2 * Real.log (f x ^ 2) ∂μ) = ∫ y, g y ^ 2 * Real.log (g y ^ 2) ∂ν) :
    squareEntropy μ f = squareEntropy ν g := by
  simp only [squareEntropy, hsq, hlog]

end
end GinibrePoincare
