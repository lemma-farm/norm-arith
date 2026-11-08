module

public import GinibrePoincare.Analysis.MatrixLocalSpectrum
public import Mathlib
@[expose] public section

/-! # The actual Gaussian matrix spectral pushforward

This constructs the law from the matrix ensemble. Identifying its density with the
Vandermonde density is a separate change-of-variables theorem.
-/
open MeasureTheory Matrix
set_option backward.isDefEq.respectTransparency false
namespace GinibrePoincare
noncomputable section

def matrixMeasurableEigenvalues (n : ℕ) : GinibreMatrixCoordinates n → Fin n → ℂ :=
  (matrix_exists_measurable_simple_labeling n).choose

theorem matrixMeasurableEigenvalues_measurable (n : ℕ) :
    Measurable (matrixMeasurableEigenvalues n) :=
  (matrix_exists_measurable_simple_labeling n).choose_spec.1

theorem matrixMeasurableEigenvalues_spec (n : ℕ) (A : GinibreMatrixCoordinates n)
    (hA : (Matrix.of A).charpoly.Separable) :
    Function.Injective (matrixMeasurableEigenvalues n A) ∧
      ∀ i, (Matrix.of A).charpoly.eval (matrixMeasurableEigenvalues n A i) = 0 :=
  (matrix_exists_measurable_simple_labeling n).choose_spec.2 A hA

def matrixSpectralMeasure (n : ℕ) : Measure (Fin n → ℂ) :=
  (matrixGaussianMeasure n).map (matrixMeasurableEigenvalues n)

instance matrixSpectralMeasure_isProbability (n : ℕ) :
    IsProbabilityMeasure (matrixSpectralMeasure n) := by
  constructor
  rw [matrixSpectralMeasure, Measure.map_apply (matrixMeasurableEigenvalues_measurable n)
    MeasurableSet.univ]
  exact matrixGaussianMeasure_univ n

                                                          
                                                                                         
                                                                                    
                                                                   
                                               

                                                   
                                                             
                            
                                                                           
       
                                                        
                                                                 
             
                                                                        
                   
                     
                              
                            
                                               
                         
                                                      
             
                                
             
                                
             
                          
                  
                                                                           
                                                                              
                                                                                             
                                                                      
                                                                       
            

                                                      
                                               
end
end GinibrePoincare
