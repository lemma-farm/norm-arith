module

public import DirectedCycles.LocalGroupProducts
public import DirectedCycles.LocalQuotientCancellation
public import DirectedCycles.LocalGroupUltraproduct

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles
namespace LocalGroupAlgebra
variable {G : Type*} (L : LocalGroupAlgebra G)

/-- Reversal includes existence of the inverse product, not only an equality
conditional on that product being defined. -/
def Reversible : Prop := ∀ {a b c}, L.mulRel a b c → L.mulRel (L.inv b) (L.inv a) (L.inv c)

                                                                               
               
                      
                     
                                                   

theorem Reversible.restrict (hL : L.Reversible) (S : Set G) (h1 : L.one ∈ S)
    (hi : ∀ x ∈ S, L.inv x ∈ S) : (L.restrict S h1 hi).Reversible :=
  fun h => hL h

                                                                              
                                        
              
              
                                
                    
                      
                      
                      
                      
             
                                       
                                      

                                                                                                       
                  
                            
                                            
                                                       
                                               
                                                                                    
                         
                                              
                                            
                                                                      
                                                    
                                                    
                                                                                
                         
                                              
                                            
                                                                      
                                                    
                                                    
                                                                                
                         
                                              
                                            
                                                                      
                                                    
                                                    
                                                   
end LocalGroupAlgebra

open scoped Pointwise
namespace LocalNormalSet
variable {G : Type*} [Group G] {P V W : Set G} (hP : LocalNormalSet P V)
    (hW1 : (1 : G) ∈ W) (hWi : W⁻¹ = W) (hW6 : W^6 ⊆ V)

                                                                                   
                                         
end LocalNormalSet

variable {ι : Type*} (F : Filter ι) (G : ι → Type*) (L : ∀ i, LocalGroupAlgebra (G i))

                                                                   
                                              
             
                                       
               
                                               
                                                      
                                   
end DirectedCycles
