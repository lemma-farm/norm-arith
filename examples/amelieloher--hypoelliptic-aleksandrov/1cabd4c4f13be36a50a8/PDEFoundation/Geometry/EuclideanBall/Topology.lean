module

public import PDEFoundation.Geometry.EuclideanBall.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Pi

/-!
# Topology of round balls on native vectors

Continuity, openness, closedness, and compactness for the explicit round
balls. Any occurrence of the inherited metric below is explicitly a
finite-product supremum-metric comparison.
-/

@[expose] public section

open Set

namespace PDE

theorem contDiff_vecNormSq {d : ℕ} :
    ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec d => vecNormSq x) := by
  unfold vecNormSq vecDot
  exact ContDiff.sum (s := Finset.univ) fun i _hi =>
    (contDiff_apply ℝ (fun _ => ℝ) i).mul (contDiff_apply ℝ (fun _ => ℝ) i)

                                      
                                                
                               

                                             
                                                          
                                                      

                                             
                                                       
                                        

theorem contDiff_euclideanSqDist_left {d : ℕ} (x₀ : Vec d) :
    ContDiff ℝ (⊤ : ℕ∞)
      (fun x : Vec d => euclideanSqDist x x₀) := by
  unfold euclideanSqDist
  exact contDiff_vecNormSq.comp (contDiff_id.sub contDiff_const)

theorem continuous_euclideanSqDist_left {d : ℕ} (x₀ : Vec d) :
    Continuous (fun x : Vec d => euclideanSqDist x x₀) :=
  (contDiff_euclideanSqDist_left x₀).continuous

theorem isOpen_euclideanBall {d : ℕ} (x₀ : Vec d) (R : ℝ) :
    IsOpen (euclideanBall x₀ R) := by
  change IsOpen
    ((fun x : Vec d => euclideanSqDist x x₀) ⁻¹' Iio (R ^ 2))
  exact isOpen_Iio.preimage (continuous_euclideanSqDist_left x₀)

theorem measurableSet_euclideanBall {d : ℕ}
    (x₀ : Vec d) (R : ℝ) :
    MeasurableSet (euclideanBall x₀ R) :=
  (isOpen_euclideanBall x₀ R).measurableSet

                                            
                          
                                             
                 
                                                             
                                                                  

                                                 
                          
                                               
                                                   

                                        
                          
                                         
                 
                                                         
                                   
                                        

                                               
                               
                                               
                                             
                                   

                                                                     
                                                
                                                        
                                       
                                                           
            
                                               
         
                                         
                                                     
                                 
                              
                                               

                                                                        
                                      
                                            
                                       
                                               
            
                                         
         
                                         
                                                        
                                 
                                 
                                               

                                             
                                       
                                           
                                                            
                                       
                                                 

end PDE
