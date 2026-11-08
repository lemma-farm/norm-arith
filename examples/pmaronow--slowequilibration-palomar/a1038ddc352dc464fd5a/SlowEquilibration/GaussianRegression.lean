-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianDensity
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Probability.Distributions.Gaussian.Fernique
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
public import Mathlib.Probability.Kernel.Composition.MeasureComp
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Invertible
public import Mathlib.Tactic.FunProp

/-!
# Canonical whole-field finite Gaussian regression

The observation is an actual surjective continuous linear map of a genuine
standard Gaussian coefficient vector. Its canonical lift, orthogonal residual,
independence, and full Borel regression kernel are derived, not assumed.
-/

@[expose] public section

namespace SlowEquilibration.GaussianRegression

open MeasureTheory ProbabilityTheory Set Function
open scoped RealInnerProductSpace Topology ENNReal

noncomputable section

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]

/-- The genuine observation covariance operator. -/
def gram (A : E →L[ℝ] F) : F →L[ℝ] F := A.comp A.adjoint

/-- The ordinary canonical minimum-norm lift. -/
def lift (A : E →L[ℝ] F) : F →L[ℝ] E := A.adjoint.comp (gram A).inverse

/-- The ordinary full-coefficient residual, before its projection property is proved. -/
def residual (A : E →L[ℝ] F) : E →L[ℝ] E := ContinuousLinearMap.id ℝ E - (lift A).comp A

                                                                             
                                                                       
                                                                                           
                                                        
                                   
                                 
        
                                                             
                                    
                                    
                                                  
                                                       
                                                  
                                        

                                                                             
                                                            
                                                      
             
                                       
                                                  

                                                                             
                                                                          
                          
                                                                       
         

                                                                             
                                                                                               
                             
                                                                                               
                                                   

                                                                             
                                                                            
                                  
                          
                                                                                        

                                                                             
                                                                                   
                                                                        
                                           
                               
         
      
                                                                                     
            
                                                 
                                                                                                 
                     
                          
                                        

                                                                             
                                                                              
                                                 
                                                                                              
                                       
           
                                                   
                                                    
                                                                                             
            
                                        
                                                     
                                                                                   
            
                                         
                                                                     
                                                                            
                                                           
                          

                                   
def observationLaw (A : E →L[ℝ] F) : Measure F := (stdGaussian E).map A

/-- The genuine full residual law, including all unobserved field coefficients. -/
def residualLaw (A : E →L[ℝ] F) : Measure E := (stdGaussian E).map (residual A)

instance observationLaw_probability (A : E →L[ℝ] F) : IsProbabilityMeasure (observationLaw A) := by
  unfold observationLaw
  infer_instance

instance residualLaw_probability (A : E →L[ℝ] F) : IsProbabilityMeasure (residualLaw A) := by
  unfold residualLaw
  infer_instance

                                                                                        
                                                                           
                                                        
                                                
                                                                       
                                                                                        

                                                                            
                                                                   
def regressionKernel (A : E →L[ℝ] F) : Kernel F E where
  toFun w := (stdGaussian E).map (fun x => residual A x + lift A w)
  measurable' := by
    rw [Measure.measurable_measure]
    intro s hs
    simp only [Measure.map_apply (by fun_prop : Measurable
      (fun x : E => residual A x + lift A _)) hs]
    exact measurable_measure_prodMk_left (s := {p : F × E | residual A p.2 + lift A p.1 ∈ s})
      (hs.preimage (by fun_prop))

@[simp] lemma regressionKernel_apply (A : E →L[ℝ] F) (w : F) :
    regressionKernel A w = (stdGaussian E).map (fun x => residual A x + lift A w) := rfl

instance regressionKernel_markov (A : E →L[ℝ] F) : IsMarkovKernel (regressionKernel A) where
  isProbabilityMeasure w := by
    rw [regressionKernel_apply]
    infer_instance

                                                                             
                                                                        
                                                     
                                                                                         
                                         
                                           
                                                           
                   

                                                                             
                                                                            
                                                             
                                         
                                                               
                                                   

                                                                              
                                                   
                                                                        
                                             
                                                   
                                                
                                           
                                                
         
          
                
       
                                                  

                                                                            
                                                                    
                                                                     
                                                  
                                         
                                                                          
      
                                                               
                                             
                                                                                
                                                                            
                                                                   
               
                           
             
                                                                  
                                                                                
                                                       
                                                         
                                              
                                                            
                                       

                                                                             
                                                                                 
                                                                 
                                                                                                    
                                
                
                                                                        
                                               

                                                                             
                                                     
                                                                                     
                                             
                             
                                               
                                                           
                                                                         
                                                                          

end
end SlowEquilibration.GaussianRegression
