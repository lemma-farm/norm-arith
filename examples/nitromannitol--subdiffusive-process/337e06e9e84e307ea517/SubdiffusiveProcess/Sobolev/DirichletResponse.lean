module

public import SubdiffusiveProcess.Sobolev.ResponseComparison
public import SubdiffusiveProcess.Sobolev.ResponsePositivity

@[expose] public section

/-!
# Canonical boundary responses

Boundary data are actual elements of the weak H1 graph. Admissible functions
differ by an element of the concrete variation space; for the killed space
this is the usual H1/H1_0 boundary class. The minimizer is constructed from
the source solver with load -E(b, ·), and the minimum is proved attained.
-/

open MeasureTheory InnerProductSpace Filter Set TopologicalSpace
open scoped ENNReal NNReal
noncomputable section
namespace SubdiffusiveProcess
variable {d : ℕ} {Ω : Opens (SpatialCoordinates d)}

/-- The actual coefficient form on full function/gradient data. -/
def sobolevCoefficientForm (a : PositiveCoefficient Ω) :
    SobolevData Ω →L[ℝ] SobolevData Ω →L[ℝ] ℝ :=
  (weightedGradientForm a.val).bilinearComp sobolevGradient sobolevGradient

/-- Symmetry also holds before imposing killed or mean-zero variations. -/
theorem sobolevCoefficientForm_symm (a : PositiveCoefficient Ω) (u v : SobolevData Ω) :
    sobolevCoefficientForm a u v = sobolevCoefficientForm a v u :=
  weightedGradientForm_symm a.val _ _

/-- Full gradient energies are nonnegative, without a Poincare condition. -/
theorem sobolevCoefficientForm_nonneg (a : PositiveCoefficient Ω) (u : SobolevData Ω) :
    0 ≤ sobolevCoefficientForm a u u := by
  obtain ⟨c, hc, ha⟩ := a.property
  obtain ⟨c', hc', hb⟩ := weightedGradientForm_coercive a.val hc ha
  exact (mul_nonneg (mul_nonneg hc'.le (norm_nonneg _)) (norm_nonneg _)).trans (hb _)

/-- The load that corrects a given H1 extension to a harmonic one. -/
def boundaryCorrectionLoad (S : ResponseSpace Ω) (a : PositiveCoefficient Ω)
    (b : weakSobolevGraph Ω) : S.space →L[ℝ] ℝ :=
  -((sobolevCoefficientForm a b.val).comp S.space.subtypeL)

/-- The actual harmonic extension in the given affine Sobolev class. -/
def dirichletMinimizer (S : ResponseSpace Ω) (a : PositiveCoefficient Ω)
    (b : weakSobolevGraph Ω) : weakSobolevGraph Ω :=
  ⟨b.val + (responseSolution S a (boundaryCorrectionLoad S a b) : SobolevData Ω),
    (weakSobolevGraph Ω).add_mem b.property (S.le_weak (responseSolution S a _).property)⟩

                                                               
                                                                                       
                              
                                                          
                                                            
                                                                  

                                                                       
theorem dirichletMinimizer_euler (S : ResponseSpace Ω) (a : PositiveCoefficient Ω)
    (b : weakSobolevGraph Ω) (w : S.space) :
    sobolevCoefficientForm a (dirichletMinimizer S a b).val w.val = 0 := by
  have he := responseSolution_spec S a (boundaryCorrectionLoad S a b) w
  change sobolevCoefficientForm a (responseSolution S a (boundaryCorrectionLoad S a b)).val w.val =
    -(sobolevCoefficientForm a b.val w.val) at he
  change sobolevCoefficientForm a (b.val + (responseSolution S a (boundaryCorrectionLoad S a b)).val)
    w.val = 0
  rw [map_add, add_apply, he, add_neg_cancel]

/-- The scalar boundary response is the actual energy of its constructed extension. -/
def dirichletResponse (S : ResponseSpace Ω) (a : PositiveCoefficient Ω)
    (b : weakSobolevGraph Ω) : ℝ :=
  sobolevCoefficientForm a (dirichletMinimizer S a b).val (dirichletMinimizer S a b).val

/-- Every admissible competitor loses exactly the energy of its difference from the minimizer. -/
theorem dirichletResponse_energy_gap (S : ResponseSpace Ω) (a : PositiveCoefficient Ω)
    (b : weakSobolevGraph Ω) (w : S.space) :
    sobolevCoefficientForm a (b.val + w.val) (b.val + w.val) =
      dirichletResponse S a b + sobolevCoefficientForm a
        (b.val + w.val - (dirichletMinimizer S a b).val)
        (b.val + w.val - (dirichletMinimizer S a b).val) := by
  apply bilinear_affine_energy_gap _ (sobolevCoefficientForm_symm a)
  have he := dirichletMinimizer_euler S a b
    (w - responseSolution S a (boundaryCorrectionLoad S a b))
  simpa only [dirichletMinimizer, Submodule.coe_sub, add_sub_add_left_eq_sub] using he

/-- The boundary variational formula is an attained least value. -/
theorem dirichletResponse_isLeast (S : ResponseSpace Ω) (a : PositiveCoefficient Ω)
    (b : weakSobolevGraph Ω) :
    IsLeast (Set.range fun w : S.space =>
      sobolevCoefficientForm a (b.val + w.val) (b.val + w.val)) (dirichletResponse S a b) := by
  constructor
  · exact ⟨responseSolution S a (boundaryCorrectionLoad S a b), rfl⟩
  · rintro x ⟨w, rfl⟩
    change dirichletResponse S a b ≤ sobolevCoefficientForm a (b.val + w.val) (b.val + w.val)
    rw [dirichletResponse_energy_gap]
    exact le_add_of_nonneg_right (sobolevCoefficientForm_nonneg a _)

                                                                
                                                                                  
                                                                                               

                                                                    
                                                                                   
                                          
                                                                                                 
                                                        
                                                 
                                    
                                                      
                                                                
                                             
                                                       
                               
                                                               
                                                                         
                                   
                                                                   
                                                                       
                                                                                        
                                                                            
                                                      

                                                                                        
                                                                                        
                                                             
                                                                    
                                      
                                                                
                                                                            
         
                                          
                                                                                      
                                                                                
                                                        
                                                        
                   
                                                               

                                                                                     
                                                                                          
                                                                
                                                             
                                      
                                                                             
        
                                        

                                                                                    
                                                                                         
                                                                
                                                           
                          
                                                   

                                                                          
                              
                                              
                                                     
                                
                                    
                                                               
      
                                      
                                                                            
                               
                                                                 
                                                   
        
           
                                   
                                                                                 
                           
                                                                   

                                                                            
                               
                                              
                                                     
                                      
                                                                       
      
                                      
                                                                   
                               
                                                              
           
                                                                                  
                             
                                          

end SubdiffusiveProcess
