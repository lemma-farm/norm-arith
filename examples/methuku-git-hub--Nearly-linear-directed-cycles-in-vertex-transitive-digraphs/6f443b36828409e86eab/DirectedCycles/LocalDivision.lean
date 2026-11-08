module

public import DirectedCycles.LocalGroupReversal

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles
namespace LocalGroupAlgebra
variable {G : Type*} (L : LocalGroupAlgebra G)

/-- A defined product can be solved for either factor inside the actual local
multiplication domain. This is an existence property, stronger than equality
of values conditional on the inverse products already being defined. -/
structure DivisionClosed : Prop where
  left : ∀ {a b c}, L.mulRel a b c → L.mulRel (L.inv a) c b
  right : ∀ {a b c}, L.mulRel a b c → L.mulRel c (L.inv b) a

                                                                                       
            
                 
                    
                       
                                
             
                 
                    
                       
                                 

theorem DivisionClosed.restrict (hL : L.DivisionClosed) (S : Set G)
    (h1 : L.one ∈ S) (hi : ∀ x ∈ S, L.inv x ∈ S) :
    (L.restrict S h1 hi).DivisionClosed := ⟨fun h => hL.left h,fun h => hL.right h⟩

                                                                                 
                        
                                                       
                                                          
                                        
end LocalGroupAlgebra

open scoped Pointwise
namespace LocalNormalSet
variable {G : Type*} [Group G] {P V W : Set G} (hP : LocalNormalSet P V)
    (hW1 : (1 : G) ∈ W) (hWi : W⁻¹ = W) (hW6 : W^6 ⊆ V)

                                                                   
                                        
                                                         
            
                 
                                       
                                                                       
                                  
             
                 
                                       
                                                                       
                                   
end LocalNormalSet

variable {ι : Type*} (F : Filter ι) (G : ι → Type*) (L : ∀ i, LocalGroupAlgebra (G i))

                                                                           
                                                  
            
               
                                         
                 
                                                 
                                                                                     
             
               
                                         
                 
                                                 
                                                                                      
end DirectedCycles
