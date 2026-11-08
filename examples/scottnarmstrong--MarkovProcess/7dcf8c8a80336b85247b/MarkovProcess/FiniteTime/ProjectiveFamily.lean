/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import MarkovProcess.FiniteTime.KernelRestriction
import Mathlib.Data.Finset.Sort
import Mathlib.MeasureTheory.Constructions.Projective

/-!
# Finite-set finite-time laws

This file reindexes the ordered finite-time kernels by finite sets of times and proves their
Mathlib-native projectivity. It does not assert or construct a projective-limit measure.
-/

open MeasureTheory ProbabilityTheory

namespace MarkovProcess
namespace SubMarkovKernelSemigroup

variable {α : Type*} [MeasurableSpace α]

/-- The increasing enumeration of a finite set of nonnegative times. -/
noncomputable def finiteSetTimes (I : Finset NNReal) : FiniteOrderedTimes I.card :=
  I.orderEmbOfFin rfl

/-- Reindex an ordered coordinate path by its finite set of times. -/
noncomputable def orderedPathToFiniteSet (I : Finset NNReal) (path : Fin I.card → α) : I → α :=
  fun t ↦ path ((I.orderIsoOfFin rfl).symm t)

/-- Reindexing an ordered coordinate path by its finite set of times is measurable. -/
theorem measurable_orderedPathToFiniteSet (I : Finset NNReal) :
    Measurable (orderedPathToFiniteSet (α := α) I) :=
  measurable_pi_iff.mpr fun t ↦ measurable_pi_apply ((I.orderIsoOfFin rfl).symm t)

/-- The finite-time kernel indexed by a finite set of times. -/
noncomputable def finiteSetKernel (P : SubMarkovKernelSemigroup α) (I : Finset NNReal) :
    Kernel α (I → α) :=
  Kernel.mapOfMeasurable (finiteTimeKernel P (finiteSetTimes I))
    (orderedPathToFiniteSet I) (measurable_orderedPathToFiniteSet I)

/-- The finite-set kernel agrees with the ordinary kernel map. -/
theorem finiteSetKernel_eq_map (P : SubMarkovKernelSemigroup α) (I : Finset NNReal) :
    finiteSetKernel P I =
      (finiteTimeKernel P (finiteSetTimes I)).map (orderedPathToFiniteSet I) :=
  Kernel.mapOfMeasurable_eq_map _ (measurable_orderedPathToFiniteSet I)

                                              
                                                                                   
                                
                       

                                                                                 
                               
                                                 
                                
                                                                       
                                               

                                                                             
                                                                                
                        
         
                                
                                 
                                                                                
                                                      
                                

                           
                                                                                     
                                                                               
                                
                                                                     
               
                                                                
                                                               
                                                                            
                                                             
     

namespace IsConservative

/-- Under conservativity, every finite-set kernel is a Markov kernel. -/
theorem isMarkovKernel_finiteSetKernel (P : SubMarkovKernelSemigroup α)
    (hP : P.IsConservative) (I : Finset NNReal) : IsMarkovKernel (finiteSetKernel P I) := by
  rw [finiteSetKernel_eq_map]
  let : IsMarkovKernel (finiteTimeKernel P (finiteSetTimes I)) :=
    hP.isMarkovKernel_finiteTimeKernel P (finiteSetTimes I)
  exact Kernel.IsMarkovKernel.map _ (measurable_orderedPathToFiniteSet I)

                                                                           
                                                                          
                                                         
                                                   
                                                                                     
                                             

                                                                                          
                                                                      
                                                                 
                         
                                                                             
                                                                              
                                                                   
                                                                   
                                                               
                                                                              
                                               
                                             
                                                          

                                                                                        
                                                                               
                                     
                                                       
                                                        
               
                                
                                                                               
                                                                              
                                                 
                                            

end IsConservative
end SubMarkovKernelSemigroup
end MarkovProcess
