module

public import SphericalAging.HardSphereStochastic
public import SphericalAging.AdaptedContinuous
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Topology.MetricSpace.Contracting

public section

/-! The genuine Ito Volterra operator on predictable product L².
Its image is obtained from an adapted continuous version and a deterministic
time cut. Product square integrability is proved by Fubini from the actual
fixed-time Ito isometry. -/

noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal InnerProductSpace

namespace SphericalAging.PredictableItoTime

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {B : ℝ≥0 → Ω → ℝ}

omit [IsProbabilityMeasure P] in
theorem integral_sq_toLp (H : Ω → ℝ) (hH : MemLp H 2 P) :
    ∫ omega, H omega ^ 2 ∂P = ‖hH.toLp H‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hH.coeFn_toLp] with omega homega
  simp only [homega, RCLike.inner_apply, conj_trivial, pow_two]

                                                          
                               
                                                        
                                          
                                                    
                                                           
                                               
                                                                                 
                                               
                                               
                                               
             
                                 
                               
                                                                                              
                               
                                                                                 
                                                                           
                                                                           
                                     
                                                                                        
                                                             
                                                        
                     
                                 
                               
                                                                                       
                                                              
                                                                                       
                                         
                                                               
                                                                           

                                 
                                                                     
                                                                              
                                                                            
                                                                        
                                                         
                   
                                                                                     
                        
                                                                                      
                                                                                         
                                                

                                                                                          
                                                                              
                                                                        

                                                              
                                                                                   
                                                                                         
                                                              

                                                                     
                                                                                   
                                                                    
                                                                        
                                                                                    
                                                              

                                                    
                                                                                   
                                              
                                                                                   
                                                                     
                                                                           
                                                   
                                                                                

                                                    
                                                                                   
                                              
                                                  
                                                                
                                                                                            

                                                   
                                                                                   
                                              
                                                    
                                                                                    
                           
              
                                                                
                                                

                                                            
                                                                                   
                                              
                                                                                       
                                                 
                                                                                          
                                                                           
                                              
         
                      
                                                                   
                                            

                                                                        
                                                                           
                                                                                           
                                                       
                                                                
                                                          
                                                                       
                                                                                     
                                                                                      
                                                                        

                                                       
                                                                                   
                                              
                                            
                                                               
                                                     
                                                                    
                                                                         
                                         
                                                                  
                          
                                                         
                                                              
                                 
                                                                      
                                                                
           
             
                             
                                                                                         
                                                                                      
                                                          
                  
                                            

                                                                        
                                                         
                                                       
                                                                                   
                                              
                                                                
                                                                                       
                                                              
                                                                               
                                            

theorem continuous_processes_ae_eq_of_fixedTime {Y Z : ℝ≥0 → Ω → ℝ}
    (hY : ∀ᵐ omega ∂P, Continuous (fun t => Y t omega))
    (hZ : ∀ᵐ omega ∂P, Continuous (fun t => Z t omega))
    (hfixed : ∀ t, Y t =ᵐ[P] Z t) :
    ∀ᵐ omega ∂P, ∀ t, Y t omega = Z t omega := by
  have hgrid : ∀ᵐ omega ∂P, ∀ n k : ℕ,
      Y (SphericalAging.AdaptedContinuous.gridTime n k) omega =
        Z (SphericalAging.AdaptedContinuous.gridTime n k) omega :=
    ae_all_iff.2 (fun n => ae_all_iff.2 (fun k => hfixed _))
  filter_upwards [hY, hZ, hgrid] with omega hy hz hg
  intro t
  exact (SphericalAging.AdaptedContinuous.adaptedVersion_eq_continuous
    (fun _ _ => rfl) hy t).symm.trans
      (SphericalAging.AdaptedContinuous.adaptedVersion_eq_continuous hg hz t)

                                                     
                                                                                   
                                      
                                                                   
                                                                                         
                                                                                     
                                            
                                                          
                                                          
                                               
                                                                                 
                         
         
                                                                                                   
                            

                                                   
                                                                                   
                                                
                                            
                                                                               
                   
              
                                                  
                                                                                           
                                                                                   
                                                               
                                                               
                                                                     
                                                                 
                          
                                                                                         
                                                           
                                                             
                            
                                                                                              
                                                                              
                                                                              
             
                                                       
           
                
        

                                                           
                                                                                   
                                                
                                                                           
                                 
                        
                                                      

variable {N : ℕ}

                                                                                                   
                                                                             
                                      
                                                                      
                               
                                                                                
                                                                     

                                                                        
                                                                          
                                            
                                                                            
                                                                 
                                      
                                                                        
                                                                                 
                                     
                                 
      
                     
                                                                          
                                                                             
                                                                               
                            
                                            
                               
                                                                                       
                            
                    

@[expose] def scalarToStatePredictable (i : Fin N) (U : PredictableProcessL2 F P) :
    SphericalAging.HardSphereDynamics.PredictableStateL2 N F P := by
  let L := ContinuousLinearMap.toSpanSingleton ℝ (SphericalAging.HardSphereDynamics.basisVector i)
  refine ⟨L.compLp (U : TimeProcessL2 P), ?_⟩
  have hcoe : (L.compLp (U : TimeProcessL2 P) : ℝ≥0 × Ω →
      SphericalAging.HardSphereDynamics.State N) =ᵐ[nonnegativeLebesgueMeasure.prod P]
      (fun a => L ((U : TimeProcessL2 P) a)) := L.coeFn_compLp (U : TimeProcessL2 P)
  exact (L.continuous.comp_aestronglyMeasurable (lpMeas.aestronglyMeasurable U)).congr hcoe.symm

theorem scalarToStatePredictable_sub (i : Fin N) (U V : PredictableProcessL2 F P) :
    scalarToStatePredictable i (U - V) = scalarToStatePredictable i U - scalarToStatePredictable i V := by
  apply Subtype.ext
  exact (ContinuousLinearMap.toSpanSingleton ℝ (SphericalAging.HardSphereDynamics.basisVector i)).compLpL
    2 (nonnegativeLebesgueMeasure.prod P) |>.map_sub (U : TimeProcessL2 P) (V : TimeProcessL2 P)

                                                                                     
                                              
                                                 
                                                                                                               
                                                  
                                                                                           
                                                       
                                                                              
                              

                                                                                               
                                                                                 
                                                   
                                                                      
                                                                 
                                         
                                                            

                                                                          
                                                                         
                                        
                                                                
                                                                                 
                                                   
                                                                        
                                                                     
                                                 
                             
                               
      
                                                
                                                                    
                                  
                                                                                      
                                                                 
                             
               
                                         
          
                                                                       
                                                                        
                                              
                                                                     
                                                            
                                       
                               
                                                      
                                                                                                
                        
                          

                                                                        
                                                                     
                                                                            
                                           
                                                                
                                                                                 
                                                   
                                                                    
                                                    
                                                                      
                                                 
                                                                              
                           
                                                                                
                                     
                                                                   
                                      
             
                                                                         
                                                              
                                                 
                                                                               
                                                          
            
                                    

end SphericalAging.PredictableItoTime
