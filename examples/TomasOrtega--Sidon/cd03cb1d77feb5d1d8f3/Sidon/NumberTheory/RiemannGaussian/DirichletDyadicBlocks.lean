module

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Analysis.Analytic.ChangeOrigin
public import Mathlib.Analysis.Analytic.Uniqueness
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Nat.ChineseRemainder
public import Mathlib.Data.Nat.Periodic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.NumberTheory.LSeries.SumCoeff
public import Mathlib.NumberTheory.SumPrimeReciprocals
public import Mathlib.Probability.Moments.MGFAnalytic
public import Mathlib.Tactic
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Group
public import Sidon.NumberTheory.RiemannGaussian.RiemannXiSuzukiPositiveCriticalStripEtaFiniteApproximation
public import Sidon.NumberTheory.RiemannGaussian.RiemannXiSuzukiSpectralStaticContourCriticalZetaUpper
public import Sidon.NumberTheory.RiemannGaussian.ZetaPrimeGram
public import Sidon.NumberTheory.RiemannGaussian.ZetaPrimeMomentEnvelope

@[expose] public section

namespace RiemannGaussian.DirichletDyadicBlocks
noncomputable section
open scoped Classical

def positivePrefix (s : ℂ) (M : ℕ) : ℂ :=
  ∑ n ∈ Finset.Ico 1 M, zetaPrimeFeature s n

def block (s : ℂ) (j : ℕ) : ℂ :=
  ∑ n ∈ Finset.range (2 ^ j), zetaPrimeFeature s (2 ^ j + n)

theorem feature_eq_cpow (s : ℂ) {n : ℕ} (hn : 0 < n) :
    zetaPrimeFeature s n = (n : ℂ) ^ (-s) := by
  rw [zetaPrimeFeature, Complex.cpow_def_of_ne_zero (Nat.cast_ne_zero.mpr hn.ne'),
    ← Complex.natCast_log]
  congr 1
  ring

                                                                 
                                                                                  
                         
                                                                                       
                                                          

                                                     
                                                 
                                                                      
         
      

                                                  
                                                                           
                              

                                      
                                                                                  
                                  
                                                                  
         
     

                                        
                                                                    
                  
                                 
                
                                                  
                                                                   
                                     

                                              
                              
                                                                           
                                                                 
                                                          

                                       
                                                                
                                                               
                  
                                                          
                
                                                 
                                                                 
                               
                                     
                                                            
               
                                                        
                                                  
                                              
                                                                             
                                                      
                                                
             
        

                                               
                                       
                                               
                                                                      
                                                
                                                        
                                                                     
                                                                                
                   
                          
                                                                 
                     
                                         
      

end
end RiemannGaussian.DirichletDyadicBlocks
