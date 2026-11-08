/- Native metric adapters for the sharp compact sector estimate. -/
module
public import Glennie.Sector
public import Glennie.Hilbert
public import Glennie.Theorems.MatrixDetEstimate

@[expose] public section
namespace Glennie
noncomputable section

theorem diagonalAlbert_inner (a b c : ℝ) :
    inner (diagonalAlbert a b c) (diagonalAlbert a b c) = a^2+b^2+c^2 := by
  simp [inner_coordinates, diagonalAlbert, octDot_coordinates, octNormSq, Quaternion.normSq_def']
  ring

theorem complexAlbert_inner (a b c : ℝ) (u v w : ℂ) :
    inner (complexAlbert a b c u v w) (complexAlbert a b c u v w) =
      a^2+b^2+c^2+2*(Complex.normSq u+Complex.normSq v+Complex.normSq w) := by
  simp [inner_coordinates, complexAlbert, complexOct, octDot_coordinates,
    octNormSq, Quaternion.normSq_def', Complex.normSq_apply]
  ring

theorem sectorFrobeniusSq_eq (M : Matrix (Fin 3) (Fin 3) ℂ) :
    sectorFrobeniusSq M = MatrixDetEstimate.frobeniusSq M := by
  simp [sectorFrobeniusSq, MatrixDetEstimate.frobeniusSq,
    MatrixDetEstimate.columnGram, Matrix.trace, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Fin.sum_univ_three,
    Complex.normSq_apply, Complex.mul_re]
  ring

theorem inner_hidden_decomposition (z : Albert) :
    inner z z = inner (complexProjection z) (complexProjection z)+
      2*sectorFrobeniusSq (hiddenMatrix z) := by
  calc
    _ = inner (complexProjection z+hiddenAlbert (hiddenMatrix z))
        (complexProjection z+hiddenAlbert (hiddenMatrix z)) := by
      rw [complex_hidden_decomposition]
    _ = _ := by
      rw [inner_add_left, inner_add_right, inner_add_right,
        complex_hidden_orthogonal, inner_comm (hiddenAlbert _) (complexProjection _),
        complex_hidden_orthogonal, hiddenAlbert_norm]
      simp [sectorFrobeniusSq]

theorem hidden_energy_le (z : Albert) :
    2*sectorFrobeniusSq (hiddenMatrix z) ≤ inner z z := by
  rw [inner_hidden_decomposition]
  linarith [inner_self_nonneg (complexProjection z)]

                                                           
                                                             
                                         
                                                                                         
                                       
                                            
                                                                
                                                                
          
                                    
             
                                                                              
                                                                          
                             
                                                                      
                                                                         
                            
                                                     
                                                                             
                                  
                                                                                  
                                  
                                        
           

                                               
                                                       
                                                             
                                                                   
                                   
                                                           
                                  
                                                                   
                                                  
                                                        
           

end
end Glennie
