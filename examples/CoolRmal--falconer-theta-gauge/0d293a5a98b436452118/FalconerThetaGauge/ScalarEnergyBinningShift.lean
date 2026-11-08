module

public import FalconerThetaGauge.ScalarEnergyBinning
public import Mathlib.Data.Int.Interval

/-!
# Shift and dilation bounds in Lemma 7.3

The shifted pair sets are actual unions of half-open bin rectangles. Their
mass is an exact discrete correlation, so countable Cauchy--Schwarz proves
the manuscript's constants `4` and `2L+1` without discarding endpoint atoms.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Function
open scoped ENNReal

namespace FalconerThetaGauge

/-- The exact pairs whose integer bin indices differ by `m`. -/
def scalarBinShiftPairs (h : ℝ) (m : ℤ) : Set (ℝ × ℝ) :=
  ⋃ j : ℤ, scalarBin h j ×ˢ scalarBin h (j - m)

theorem measurableSet_scalarBinShiftPairs (h : ℝ) (m : ℤ) :
    MeasurableSet (scalarBinShiftPairs h m) :=
  MeasurableSet.iUnion fun j ↦ (measurableSet_scalarBin h j).prod (measurableSet_scalarBin h _)

/-- The true measure of a bin-index shift is its exact countable mass correlation. -/
theorem measure_scalarBinShiftPairs (η ζ : Measure ℝ) [SFinite ζ]
    {h : ℝ} (hh : 0 < h) (m : ℤ) :
    η.prod ζ (scalarBinShiftPairs h m) =
      ∑' j : ℤ, scalarBinMass η h j * scalarBinMass ζ h (j - m) := by
  have hdisj : Pairwise (Disjoint on fun j : ℤ ↦ scalarBin h j ×ˢ scalarBin h (j - m)) := by
    intro j k hjk
    exact (scalarBin_pairwise_disjoint hh hjk).set_prod_left _ _
  rw [scalarBinShiftPairs, measure_iUnion hdisj (fun j ↦
    (measurableSet_scalarBin h j).prod (measurableSet_scalarBin h _))]
  simp only [Measure.prod_prod, scalarBinMass]

theorem tsum_scalarBinMass_shift_square (η : Measure ℝ) (h : ℝ) (m : ℤ) :
    (∑' j : ℤ, scalarBinMass η h (j - m) ^ (2 : ℕ)) = scalarBinSquareMass η h :=
  (Equiv.subRight m).tsum_eq (fun j ↦ scalarBinMass η h j ^ (2 : ℕ))

/-- A shifted cross-bin correlation is bounded by the two true bin-square masses. -/
theorem measure_scalarBinShiftPairs_le (η ζ : Measure ℝ) [SFinite ζ]
    {h : ℝ} (hh : 0 < h) (m : ℤ) :
    η.prod ζ (scalarBinShiftPairs h m) ≤
      scalarBinSquareMass η h ^ (1 / 2 : ℝ) * scalarBinSquareMass ζ h ^ (1 / 2 : ℝ) := by
  rw [measure_scalarBinShiftPairs η ζ hh m]
  simpa only [tsum_scalarBinMass_shift_square, scalarBinSquareMass] using
    scalarBin_cauchy_schwarz (scalarBinMass η h) (fun j ↦ scalarBinMass ζ h (j - m))

                                                                         
                                                                       
                                  
                                                                      
                                                   
                                                                                            
               
         

                                                                                           
                                                                        
                                                         
                                                                     
                                                                
                                                          
              
                      
                                                                                    
                      
                                                               
                                                                
      
                                                                                   
                                                                                    
                                            
                                                                            
                                                                           

                                                                                        
                                                                     
                                
                                                 
                                                                        
                                                
                                                             
                                               
                                  
                                                 
                                                                             
                                                                      
                                                        
                                                                                       
                      
                                                                                       
                      
                                             

                                                                                     
                                                                             
                                  
                                                                       
      
                                 
                                                                                      
                                    
                                                                                                 
                                         
                                                                                          
                           
              
                                          
                                                                

                                                                                      
                                                                       
                                                  
                                                                                     
                                                
                                                             
                                  
                                                                                      
                
                                                                                     
                
                                                                             
                      
                                                                            
                      
                                             

                                                                       
                                                                         
                                  
                                             
                                                              
      
                                             
                                                                                     
                                                     
                
                                                
                                
                                                        
                                                            
                                                                      
                 
            
                                              
               
         
                                                             
                                                                

end FalconerThetaGauge
