/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.Embedding.RayIntegral
public import EllipticPdes.Embedding.Convolution
public import EllipticPdes.Sobolev.WeakDerivClassical
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
public import Mathlib.Topology.MetricSpace.HolderNorm
public import Mathlib.Tactic.Module
public import Mathlib.Analysis.Convolution
public import Mathlib.Analysis.Calculus.ContDiff.Convolution
public import Mathlib.Analysis.Calculus.BumpFunction.Normed
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Riesz-kernel `Lᵖ` bound for the Morrey embedding

For `p > d` the `(d-1)`-Riesz potential of an `Lᵖ` function over a ball of radius `R`
centred at the base point is controlled by `Cdp · R^{1-d/p} · ‖g‖_{Lᵖ}`. The exponent
`1 - d/p` is the Morrey Hölder exponent, produced here from Hölder's inequality with the
conjugate exponent `q = p/(p-1)` together with the radial `L^q` norm of the singular kernel.

The results are stated on a finite-dimensional real normed space `E` with an additive Haar
measure, for functions with values in a Banach space, and with the weak Fréchet derivative of
`EllipticPdes.HasWeakFDerivOn` (`exists_holderOnWith_of_hasWeakFDerivOn`). The statements on
`EuclideanSpace ℝ (Fin d)` with coordinate partial derivatives (`morrey_ball`,
`morrey_ball_contDiff`) are instances through the gradient functional `gradCLM`.

The kernel-norm computation is isolated in the private lemma `setIntegral_ball_dist_rpow`,
a closed-form value for the radial integral `∫_{B(x,R)} dist x y^s` over a ball centred at the
singularity, valid for `s > -d`.
-/

@[expose] public section

open MeasureTheory Set Metric
open scoped NNReal ENNReal Convolution Topology

noncomputable section

namespace EllipticPdes.Embedding

open EllipticPdes.Sobolev (partialD)

variable {d : ℕ} {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The restriction of a measure that is finite on compact sets to a ball is a finite
measure. -/
instance {X : Type*} [PseudoMetricSpace X] [ProperSpace X] {m : MeasurableSpace X}
    (μ : Measure X) [IsFiniteMeasureOnCompacts μ] (c : X) (r : ℝ) :
    IsFiniteMeasure (μ.restrict (Metric.ball c r)) :=
  isFiniteMeasure_restrict.2 measure_ball_lt_top.ne

                                                                                                
                                                                                            
                                                                                     
                                                                                                
                                                                                              
                                                                                             
                                                      
                                    
                                         
                                                     
                          
                                                       
                                          
                                                          
                                  
                                               
                            
         
                                                                                       
                                             
                                                   
                                                                      
                                                   
                                                                   
                                                                    
                                                                      
                          
                                                            
                                                   
                                                                                                 
            
                         
                                                                             
                                                            
                                                                                
                                                                
                                                                                          
                                            
                                       
                                      
                                                    
                                               
           
                                                                                  
                                                                            
              
                                 
                                                                          
                                                                               
                                                                   
                                               
                                                                         
                                                                                       
                                                                                   
                                                                
                                                
                                                                                            
                           
                                                             
                                            
      

                                                                        
                                            
             
                        
                                                                      
                        

                                                                               
                                                                                                 
                                            
                                                                                            
                                                            
                                                                                            
                          
                                                       
                                
                                       
                                     
                                                                     
                                                                         
              
                                                               
                                                                                               
              
                                                   
                                                                          
                                                            
                                    
                                                                         
                                              
                                
                                                                                      
                  
                                                           
                                  
              
                                                                                                  
                                                                            
               
                            
                           
                                                                                                 
                                                                       
                                                                             
                                                                                                
                     
                                                                        
                                                         
                                                                               
                                                           
                                                                                     
                                                                                        
                                                                                       
                                                               
                                                                                        
                                                      
                                              

                                                                                         
                                                                                        
                                                                                      
                                                     
                                                                                                   
                                           
                    
                                                                   
                                                             
                                             
                                                                                          
                          
                                                       
                                                                    
                                                                                          
                             
                                  
                                          
                                
                                                                                    
                                         
                                                  
                           
                                                        
                                                             
                                                          
                                                       
                                                                                  
                                                      
                                            
                                                            
                                                                                        
                                                                                   
                                                                                            
                                              
                                                        
                                                                                           
                                                                       
                                                
                                                          
                                                                           
                                                       
                                                                                                  
                                                            
                                                                       
                                                        
                                                             
                                                            
                                                               
                                                                            
           
                                                    
                                                                            
                                                           
                                                                             
                                                                     
                                                                             
                                                                        
                                                                               
                                                                                     
                                                                            
                                               
                                                                                   
                                                 
                                                                            
                                                                       
                                                                               
                                

                                                                                         
                                                                                      
                                                                             
                                             
                                                                        
                                                                                           
                                                          
                                         
                                                                                              
                                                       
                                                               
                                        

                                                                                          
                                                                                               
                                                                                             
                                                                                                 
                                                          
                                                                                             
                        
                                           
                    
                                                                   
                                                                
                                                 
                                               
                                                                            
                                                             
                  
                                  
                                                             
                                                                 
                                                               
            
                       
                                                           
                                                                                      
                                                                       
                                                 
                                                     
           

                                                                                                
                                                                                            
                                                                                      
                                                                                              
                                                                                      
                                                                                  
                                                                                    
                                                 
                                                                                  
                                
                                         
                                           
                                      
                               
                                                                     
                          
                                    
                                                                                              
               
        
                                      
                                                                                               
               
        
                              
                                                     
                                                       
                                
                                                      
                                                        
                              
                                               
                                                                                   
                                                                               
                                                                                           
                                                              
                                           
                                                    
                                                                                
                                               
                                 
                                   
                                                                  
                                                     
                          
              
                                 
                                     
                                                                     
                                                      
                          
              
                                 
              
                     
                                                                     
                                                                                
                                      
                                                   
                                                                                 
                                                                       
                                            
                                             
                                                               
                                                     

                                                                                            
                                                                    
                                                                                         
                                       
                                                                                                  
                 
                                                          
                                                                                              
                                              

                                                                                               
                                                                             
                                                                                              
                                                                                                 
                                                                                         
                                                                                               
                                
                                                     
                                                   
                                                                    
                                                        
                                   
                                                            
                                                                 
                                                   
                          
                                                       
                                                
                                                  
                           
                                                        
                                                             
                                                                    
                                                                                          
                                   
                                                                                      
                                                                                       
               
                                                                                  
                                             
                               
                                                                    
                                                                                          
                 
                                                                                  
                     
                                 
                                                                 
                                                                                                  
                                                                                 
                                                                                           
                
                                 
                                                                    
                                                             
                                                                     
                                                                                  
                                                                  
                                                                                
                                                                                            
                                                                                      
                                                 
                               
                                          
                                                                    
                                                                                       
                                                                             
                                                                    
                                                           
                                                                                     

                                                                                     
                                                                                            
                                                                                         
                                                                                              
                                                     
                                                                                                
                                                               
                                                                                         
                                
                                                     
                                
                    
                                                                    
                                                           
                                                        
                                                                         
                                                                                  
                                                                               
                       
             
                         
              
                                                
                    
                                                                           
                                  
                                                                          
                                                                                                 
                                                                       
                                                                                       
                       
                                                                                      
                                                                                                 
                                                                               
                        
                                                                                
                                                     
                   
           
          


                                                                                        
                                                                                                 
                                                                                               
                                                                                                
                    
                                                                             
                                                         
                                                            
                                                   
                                                               
                                                                               
                                                                        
                                                                              
             
                                                                                
                                                                    
                               
                                                                          
                                   
                          
                                                      
                                                               
                                                                                           
                                                                                 
                                
                                                                              
                                                                   
                                                 
                                                            
                                                                                                
                                                         
            
                                                                                      
                   
                                                    
                                         
                                                     
                                            
                                                                  
                                                                                        
                           
                                                                             
                              
                                    

                                                                                                   
                                                                                                 
                                                                                      
                                                                                             
                                                                                             
                                                                                        
                                     
                                                                             
                                                                                     
                                                                                
                
                               
                                                   
                                                                 
                                                                                          
                                                                     
                          
                                                                                           
                                  
                            
                                                        
                                                                              
                                                                             
                        
                  
                                           
                                                            
                                                          
                                                                                           
                                                                     
                                                            
                                                    
                                                                                    
                                                                               
                                                                          
                                                 

                                                                       
                                                                                        
                                                           
                                                                                 
                               
                                                                          
                          
                                                                                    
                        
                                                
                                                 

                                                                                        
                                                                                         
                                                                                                
                                                                                                
                                                                                    
                                                         
                                                                                                
                                
                                                                 
                                                                                        
                                                     
                                                                       
                                                                                          
                                                                              
                                                     
                                                                   
                                                     
                                             
                                                                                  
                                                             
                                                        
                                                                  
                                         
                                                                               
                                                                                    
                                                                                  
                     
                                 
                             
                                               
                                                                   
                                                                                             
                                           
                                                                                 
                                                 
                                                                  
                                                                                  
                                                               
                                              
                                                                  
                                                                           
                                                                                               
                                              
                                                                  
                                                         
                                                          

                                                                                             
                                                                                        
                                                                                              
                                                                                         
                                                                                             
                                                                                               
                                                                                     
                                                                                              
                                                                          
                                                 
                                                                                        
                                                     
                                                    
                                                                                          
                                                  
                                        
                                                                                               
                                                                            
                                     
                                                                   
                                                              
                                                                        
                                                          
                                                                        
                                                                                               
                                                                       
                                                                       
                                                                   
                                       
               
                                                      
                                                                     
                                                                    
                                                                                           
                                                               
                                                                               
                                                                        
                                                                      
                                                                    
                                                                                               
                                        
                                                                                          
                         

                                                                  

section Coordinates

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- **Operator norm bounded by the coordinate values.** On `EuclideanSpace ℝ (Fin d)` the
operator norm of a continuous linear map is at most the sum of the norms of its values on the
standard basis vectors. -/
theorem norm_le_sum_norm_apply_single (L : EuclideanSpace ℝ (Fin d) →L[ℝ] G) :
    ‖L‖ ≤ ∑ k, ‖L (EuclideanSpace.single k (1 : ℝ))‖ := by
  refine ContinuousLinearMap.opNorm_le_bound L (by positivity) (fun x => ?_)
  have hx : x = ∑ k, x k • EuclideanSpace.single k (1 : ℝ) := by
    conv_lhs => rw [← (PiLp.basisFun 2 ℝ (Fin d)).sum_repr x]
    simp only [PiLp.basisFun_repr, PiLp.basisFun_apply, EuclideanSpace.single]
  calc ‖L x‖ = ‖L (∑ k, x k • EuclideanSpace.single k (1 : ℝ))‖ := by rw [← hx]
    _ = ‖∑ k, x k • L (EuclideanSpace.single k (1 : ℝ))‖ := by
        rw [map_sum]; simp_rw [map_smul]
    _ ≤ ∑ k, ‖x k • L (EuclideanSpace.single k (1 : ℝ))‖ := norm_sum_le _ _
    _ = ∑ k, ‖x k‖ * ‖L (EuclideanSpace.single k (1 : ℝ))‖ := by simp_rw [norm_smul]
    _ ≤ ∑ k, ‖x‖ * ‖L (EuclideanSpace.single k (1 : ℝ))‖ :=
        Finset.sum_le_sum fun k _ =>
          mul_le_mul_of_nonneg_right (PiLp.norm_apply_le x k) (norm_nonneg _)
    _ = (∑ k, ‖L (EuclideanSpace.single k (1 : ℝ))‖) * ‖x‖ := by
        rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun k _ => mul_comm _ _

/-- **`Lᵖ` seminorm of an operator-valued function by its coordinate components.** For `1 ≤ p`,
the `Lᵖ` seminorm of `Φ : EuclideanSpace ℝ (Fin d) → (EuclideanSpace ℝ (Fin d) →L[ℝ] G)` is at
most the sum of the `Lᵖ` seminorms of the components `y ↦ Φ y eₖ`. -/
theorem eLpNorm_le_sum_eLpNorm_apply_single {Φ : EuclideanSpace ℝ (Fin d) →
      EuclideanSpace ℝ (Fin d) →L[ℝ] G} {m : MeasurableSpace (EuclideanSpace ℝ (Fin d))}
    {ν : Measure (EuclideanSpace ℝ (Fin d))} (hΦ : AEStronglyMeasurable Φ ν) {p : ℝ≥0∞}
    (hp : 1 ≤ p)
    (hmeas : ∀ k, AEStronglyMeasurable (fun y => Φ y (EuclideanSpace.single k (1 : ℝ))) ν) :
    eLpNorm Φ p ν ≤ ∑ k, eLpNorm (fun y => Φ y (EuclideanSpace.single k (1 : ℝ))) p ν := by
  calc eLpNorm Φ p ν
      ≤ eLpNorm (fun y => ∑ k, ‖Φ y (EuclideanSpace.single k (1 : ℝ))‖) p ν :=
        eLpNorm_mono_real hΦ fun y => norm_le_sum_norm_apply_single (Φ y)
    _ = eLpNorm (∑ k, fun y => ‖Φ y (EuclideanSpace.single k (1 : ℝ))‖) p ν := by
        refine eLpNorm_congr_ae (Filter.EventuallyEq.of_eq (funext fun y => ?_))
        rw [Finset.sum_apply]
    _ ≤ ∑ k, eLpNorm (fun y => ‖Φ y (EuclideanSpace.single k (1 : ℝ))‖) p ν :=
        eLpNorm_sum_le hp
    _ = ∑ k, eLpNorm (fun y => Φ y (EuclideanSpace.single k (1 : ℝ))) p ν :=
        Finset.sum_congr rfl fun k _ => eLpNorm_norm _ (hmeas k)

                                                                                            
                                                                            
                                                                                        
                                                                                       
                
                                                                              
                            
                                                                                       
                                                                                       
                                                                                                
                                                                

end Coordinates

                                                                                         
                                                                                       
                       
                                                                          
                                                                    
                                 
                                                                                  
                                                    
                                                                       
                                                                               
                                                                
                                              
                                                      
                                                       
                                        
                                                                                               



                                                                                                
                                                                                             
                                    
theorem eLpNorm_fderiv_le_sum_partialD {u : EuclideanSpace ℝ (Fin d) → ℝ}
    (hu : Continuous (fderiv ℝ u)) {p : ℝ≥0∞} (hp : 1 ≤ p)
    {μ : Measure (EuclideanSpace ℝ (Fin d))} (hmeas : ∀ k, AEStronglyMeasurable (partialD k u) μ) :
    eLpNorm (fderiv ℝ u) p μ ≤ ∑ k, eLpNorm (partialD k u) p μ :=
  eLpNorm_le_sum_eLpNorm_apply_single hu.aestronglyMeasurable hp hmeas

                                                                                                
                                                             
                                                                      
                                                                                       
                                                
                                                                             
                                                                                         
                                                                         
                                                                                        
                                                                         
                                                    
                                                                                           
                                                                                      
                               
                                                       
                           
     

                                                      
                                                                                           
                                                  
                                                                   
                                             
                                                                                             
                                                                    
                                                       
                 
                                                                                            
                      

                                                                                       
                                                                                               
                                                                                             
                                                                                              
                                                                                       
                                                                              
                                                
                                                               
                                                                                 
                                  
                              
                                                                 
                                  
                                           
              
                                                                        
                              
                          
                                                                                      
                                                      
                                                                                        
                                                                               
                                                            
                                                                  
                                                    
                                                               
                                                                      
                                                                      
                                                
                                                     
                                                                
                                                                                   
                                                                                      
                                                                
                                                               
                                                    
                                                                                 
                                                                            
                                                          
             
                                                                             
                                                                                                  
                          
                                                                     
                                         
                                                                                 
                                                                                      
                       


                                                                                              
                                                                                     
                                                                                                
                  
                                                                               
                                                                            
                                                       
                                                                
                                                  
                      
                                                                           
                                                                      
                                                          
                                             
                                                                                  
                                                                                 
                                                  
                                                                             
                                                                         
                                            
                                              
                                                                              

                                                                                             
                                                                                    
                            
                                                                    
                                                         
                                                                            
                                                              
                                                
                    
                                                                         
                                                                    
                                                        
                                                       
                                               

                                                                                            
                                                                                     
                                                                                    
                                                        
                                            
                                                           
                                                         
                                                   
                                                   
                                               
                                                                                 
                                           
                                          
                                                    
                    
                                                     
                                                                    
                                                         
                                                                                          
                                                                
                                          
                                             
                                                                                  
                                                                                   
                                                                                    
                               
                                                                                                
         
                                                        
                                                        
                                                             
                                                                    
                                                                                               

                                                                                 
                                                                                                  
                                                      
                                                  
                                                       
                                
                                              
           
            
          

end EllipticPdes.Embedding
