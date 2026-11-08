import QuadraticCarleson.KrauseLaceyScaleMaximal
import Mathlib
/-!
# Actual finite stopping extraction for the Krause--Lacey recursion

This is the finite version of the extraction following KL18 Lemma 3.5:
select the maximal intervals where either input average exceeds ten times
the parent average. The selected children, their packing, and the bounded
averages on the remaining collection are conclusions, not supplied stopping
or sparse hypotheses. The only structural input is laminarity of the finite
interval collection, as holds in each source dyadic grid.
-/

open Function MeasureTheory Set
open scoped ENNReal

namespace QuadraticCarleson
namespace KrauseLaceyStoppingExtraction

set_option autoImplicit false

theorem interval_eq_of_carrier_subset_of_length_le {I J : RealInterval}
    (hsub : I.carrier ⊆ J.carrier) (hlen : J.length ≤ I.length) : I = J := by
  have he := (Ioc_subset_Ioc_iff I.left_lt_right).mp hsub
  have hl : I.left = J.left := by dsimp [RealInterval.length] at hlen; linarith
  have hr : I.right = J.right := by dsimp [RealInterval.length] at hlen; linarith
  cases I
  cases J
  simp_all

/-- The literal two-function threshold-ten test in the source recursion. -/
def IsBadDescendant (f g : ℝ → ℂ) (I J : RealInterval) : Prop :=
  J.carrier ⊆ I.carrier ∧
    (10 * intervalL1Average f I < intervalL1Average f J ∨
      10 * intervalL1Average g I < intervalL1Average g J)

noncomputable def badDescendants
    (S : Finset RealInterval) (f g : ℝ → ℂ) (I : RealInterval) : Finset RealInterval := by
  classical
  exact S.filter (IsBadDescendant f g I)

/-- Inclusion-maximal bad intervals, constructed directly from the finite
candidate collection. -/
noncomputable def stoppingChildren
    (S : Finset RealInterval) (f g : ℝ → ℂ) (I : RealInterval) : Finset RealInterval := by
  classical
  exact (badDescendants S f g I).filter fun J ↦
    ∀ K ∈ badDescendants S f g I, J.carrier ⊆ K.carrier → K = J

theorem mem_badDescendants_iff
    {S : Finset RealInterval} {f g : ℝ → ℂ} {I J : RealInterval} :
    J ∈ badDescendants S f g I ↔ J ∈ S ∧ IsBadDescendant f g I J := by
  classical
  simp [badDescendants]

theorem mem_stoppingChildren_iff
    {S : Finset RealInterval} {f g : ℝ → ℂ} {I J : RealInterval} :
    J ∈ stoppingChildren S f g I ↔
      J ∈ badDescendants S f g I ∧
        ∀ K ∈ badDescendants S f g I, J.carrier ⊆ K.carrier → K = J := by
  classical
  simp [stoppingChildren]

theorem stoppingChildren_subset
    (S : Finset RealInterval) (f g : ℝ → ℂ) (I : RealInterval) :
    stoppingChildren S f g I ⊆ S := by
  intro J hJ
  exact (mem_badDescendants_iff.mp (mem_stoppingChildren_iff.mp hJ).1).1

                            
                                                                
                                                                    
                                                                  

                                                                 
                                   
                     
                                           
                                           

                                     
                                                                
                                           
                                                       

                                                                          
                                                                   
                                                      
                                          
                                                                
                                       
                                                               
           
                                                                        
                                                                     
                                                                    
                                            
                                          
                                                           
                
                                                               
                                                                          

                                                                     
                                               
theorem stoppingChildren_pairwiseDisjoint
    {S : Finset RealInterval} (f g : ℝ → ℂ) (I : RealInterval)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun J K ↦
      J.carrier ⊆ K.carrier ∨ K.carrier ⊆ J.carrier ∨ Disjoint J.carrier K.carrier) :
    Set.Pairwise (↑(stoppingChildren S f g I) : Set RealInterval)
      (Disjoint on fun J : RealInterval ↦ J.carrier) := by
  intro J hJ K hK hJK
  rcases hlam (stoppingChildren_subset S f g I hJ)
    (stoppingChildren_subset S f g I hK) hJK with hsub | hsub | hdis
  · exact (hJK ((mem_stoppingChildren_iff.mp hJ).2 K
      (mem_stoppingChildren_iff.mp hK).1 hsub).symm).elim
  · exact (hJK ((mem_stoppingChildren_iff.mp hK).2 J
      (mem_stoppingChildren_iff.mp hJ).1 hsub)).elim
  · exact hdis

/-- The remaining collection on which the local oscillatory estimate must
be proved: discard every interval contained in a selected child. -/
noncomputable def goodCollection
    (S : Finset RealInterval) (f g : ℝ → ℂ) (I : RealInterval) : Finset RealInterval := by
  classical
  exact S.filter fun J ↦ ¬ ∃ K ∈ stoppingChildren S f g I, J.carrier ⊆ K.carrier

                                                                      
                                                  
                                  
                                                                
                                           
                                       
                                                        
                                                              
           
                                      
                                             
            
                                                    
                                                
             
                
                                                        
                
                                                        

                                                                         
                                                                  
                                        
                                                              
                                                                   
                                                          
                                                                                     
                                                                 
                                                    
                                       
                                                  
                                                  
                                            

                                                  
                                                              
                                                                   
                                                          
                                                                                     
                              
                                                                                    
                                                              
                                       
                                                  
                                                  
                                            

                                    
                                                                                          
           
                                           

                                                                           
                                                                          
                                             
                                                              
                                           
                                                          
                                                                                     
                                                                             
           
                           
                                   
                                                                                     
                                                           
                                                                               
              
                        
                                                     
                                                                                  
                   
                        
             
                                                                      
                                
                   
                        
             
                                                                      
                                
                       
                                                
                                                                         
                                                                          
                                                  
                                                                           
                                     

                                 
                                                                            
           
                                              

                                                                        
                                                                         
                                         
                                                              
                                                          
                                                                                     
                                                                         
                               
           
                     
                                
                 
                                            
                                            
                                                             
                            
                                                            
                           

                                                                          
                                                               
                                    
                                                              
                                                          
                                                                                   
                            
                                                          
                                                                          
           
                                 
                                                         
                                                                                         
         
                                                                         
               
                              
                             
                              
                             
                                                                                  
                                                                 
                         
                                                     


end KrauseLaceyStoppingExtraction
end QuadraticCarleson
