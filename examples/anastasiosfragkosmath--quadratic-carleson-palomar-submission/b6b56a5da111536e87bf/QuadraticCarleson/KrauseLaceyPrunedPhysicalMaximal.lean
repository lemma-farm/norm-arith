import QuadraticCarleson.KrauseLaceyPhysicalTailPrefix
import Mathlib
/-!
# The genuine pruned physical-truncation maximal operator

Physical length tails are compared to the regenerated prefixes of the
same pruned family. The factor two comes from subtracting two prefixes.
-/

open Function MeasureTheory Set
open scoped ENNReal

namespace QuadraticCarleson
namespace KrauseLaceyBadScale

open KrauseLaceyGenerationLayers

set_option autoImplicit false
attribute [local instance] Classical.propDecidable

noncomputable def badLengthTailAction
    (S : Finset RealInterval) (f : ℝ → ℂ) (I₀ : RealInterval) (k₀ s : ℤ)
    (scale : RealInterval → ℤ) (N : Finset RealInterval) (ell : ℤ) (x : ℝ) : ℂ :=
  ∑ I ∈ N, if (2 : ℝ) ^ ell ≤ I.length then krauseLaceyLocalizedPiece 1 (scale I) I
    (badScaleInput S f I₀ k₀ (scale I + 2 - s)) x else 0

noncomputable def badLengthTailMaximal
    (S : Finset RealInterval) (f : ℝ → ℂ) (I₀ : RealInterval) (k₀ s : ℤ)
    (scale : RealInterval → ℤ) (N : Finset RealInterval) (x : ℝ) : ℝ :=
  ⨆ ell : ℤ, ‖badLengthTailAction S f I₀ k₀ s scale N ell x‖

theorem norm_badLengthTailAction_le_prefix
    {S : Finset RealInterval} (f : ℝ → ℂ) (I₀ : RealInterval) (k₀ s : ℤ)
    (scale : RealInterval → ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun J K ↦
      J.carrier ⊆ K.carrier ∨ K.carrier ⊆ J.carrier ∨ Disjoint J.carrier K.carrier)
    (N : Finset RealInterval) (hN : N ⊆ nonstandardIntervals S f I₀ k₀ s scale)
    (ell : ℤ) (x : ℝ) :
    ‖badLengthTailAction S f I₀ k₀ s scale N ell x‖ ≤
      2 * badSubcollectionPrefixMaximal S f I₀ k₀ s scale N N.card x := by
  have hNS := hN.trans (nonstandardIntervals_subset S f I₀ k₀ s scale)
  apply norm_lengthTail_le_two_generationPrefixNormMax N
    (fun I hI J hJ hne ↦ hlam (hNS hI) (hNS hJ) hne) _ ((2 : ℝ) ^ ell) x
  intro I hI hxI
  exact krauseLaceyLocalizedPiece_eq_zero_of_notMem 1 (scale I) I _
    (Finset.mem_filter.mp (hN hI)).2.1 hxI

                                      
                                                                        
                              
                                                          
                                                                                   
                                                                                         
                                                
                                                                       
                                                                                       

theorem badLengthTailMaximal_nonneg
    {S : Finset RealInterval} (f : ℝ → ℂ) (I₀ : RealInterval) (k₀ s : ℤ)
    (scale : RealInterval → ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun J K ↦
      J.carrier ⊆ K.carrier ∨ K.carrier ⊆ J.carrier ∨ Disjoint J.carrier K.carrier)
    (N : Finset RealInterval) (hN : N ⊆ nonstandardIntervals S f I₀ k₀ s scale) (x : ℝ) :
    0 ≤ badLengthTailMaximal S f I₀ k₀ s scale N x := by
  have hb : BddAbove (Set.range (fun ell : ℤ ↦
      ‖badLengthTailAction S f I₀ k₀ s scale N ell x‖)) :=
    ⟨2 * badSubcollectionPrefixMaximal S f I₀ k₀ s scale N N.card x, by
      rintro _ ⟨ell, rfl⟩
      exact norm_badLengthTailAction_le_prefix f I₀ k₀ s scale hlam N hN ell x⟩
  exact (norm_nonneg _).trans (le_ciSup hb (0 : ℤ))

                                         
                                                             
                                                                                         
                                                                        
                         
           
                                         
                                 
                                           
            
                                        
                                     
                                                     
                                                                                     
                               
                                    

                                                    
                                                                        
                                                        
                                                                     
                                                                        
                                                
                                            
                                                                                
                  
           
         
                                                                    
                                                                                   
                                                              

                                                                        
                                                                   
                                              
                                                             
                                                              
                              
                                                          
                                                                                   
                                                                              
                                                                                         
                                                   
                                                                                  
                                                 
                                                                
                                                                         
                                                         
                                          
                                                                
                                                                            
                                                                                            
                      
                      
           
                                                                                      
                                                                
                                                                             
                                                                    
                   
                                                                                     
                
                                                               
                                               
                                                   
                                                                                      
                                      


end KrauseLaceyBadScale
end QuadraticCarleson
