module

public import DirectedCycles.LocalEscapeNorm
public import DirectedCycles.LocalWordPowers

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles
namespace LocalGroupAlgebra
variable {G : Type*} (L : LocalGroupAlgebra G)

/-- A finite segment of powers, with every bracketing certified up to N.
Values beyond N are deliberately unconstrained and are never used as powers. -/
structure PowerSegment (g : G) (N : ℕ) where
  power : ℕ → G
  product : ∀ n ≤ N, L.Product (List.replicate n g) (power n)

namespace PowerSegment
variable {L} {g : G} {N : ℕ} (p : L.PowerSegment g N)

                                                                                  

theorem one (hN : 1 ≤ N) : p.power 1 = g := (Product.singleton_iff L).1 (p.product 1 hN)

                                       
                                                          
                                                                                               
                                                                  
                                                                  
                               
end PowerSegment

                                                                           
                                                  
                                                                   
                                                             
                                                                    
                    
                        
                                            

                                                             
                                                         
                                                 
                                    
                      
                                          
end LocalGroupAlgebra
end DirectedCycles
