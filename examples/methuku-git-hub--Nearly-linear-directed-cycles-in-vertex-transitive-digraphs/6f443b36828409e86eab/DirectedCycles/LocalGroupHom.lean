module

public import DirectedCycles.LocalGroupProducts
public import DirectedCycles.LocalQuotientOperations

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles

/-- A map preserves every defined multiplication, but is not required to send
undefined products to undefined products. -/
structure LocalGroupHom {G H : Type*} (L : LocalGroupAlgebra G) (M : LocalGroupAlgebra H) where
  toFun : G → H
  map_one : toFun L.one = M.one
  map_inv : ∀ x, toFun (L.inv x) = M.inv (toFun x)
  map_mul : ∀ {x y z}, L.mulRel x y z → M.mulRel (toFun x) (toFun y) (toFun z)

namespace LocalGroupAlgebra
variable {G H : Type*} {L : LocalGroupAlgebra G} {M : LocalGroupAlgebra H}

                                                                              
                                                                                      
                                               
                  
                                                                         
                                                      
                                                       
                                               
                                                                  
                                                                           
                         
                                                                                                
                                                                                                
                                                                                      
                                                                                      
                                                                        
                                 
                         
                                                                                                
                                                                                                
                                                                                      
                                                                                      
                                                                        
                                 
                         
                                                                                                
                                                                                                
                                                                                      
                                                                                      
                                                                                    
end LocalGroupAlgebra

namespace LocalGroupHom
variable {G H J : Type*} {L : LocalGroupAlgebra G} {M : LocalGroupAlgebra H} {N : LocalGroupAlgebra J}

                                                          
                    
                
                  
                

                                                                                  
                            
                                                                   
                                                                     
                                      

def inclusion (L : LocalGroupAlgebra G) (S : Set G) (h1 : L.one ∈ S)
    (hi : ∀ x ∈ S, L.inv x ∈ S) : LocalGroupHom (L.restrict S h1 hi) L where
  toFun := Subtype.val
  map_one := rfl
  map_inv _ := rfl
  map_mul h := h
end LocalGroupHom
end DirectedCycles
