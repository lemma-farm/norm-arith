module

public import GinibrePoincare.Analysis.TwoPointLSI

@[expose] public section

open scoped BigOperators
namespace GinibrePoincare
noncomputable section

/-- A recursively presented finite Bernoulli cube. -/
def BernoulliCube : ℕ → Type
  | 0 => Unit
  | n + 1 => BernoulliCube n × Bool

instance bernoulliCubeFintype : (n : ℕ) → Fintype (BernoulliCube n)
  | 0 => inferInstanceAs (Fintype Unit)
  | n + 1 => @instFintypeProd (BernoulliCube n) Bool (bernoulliCubeFintype n) inferInstance

instance bernoulliCubeNonempty : (n : ℕ) → Nonempty (BernoulliCube n)
  | 0 => inferInstanceAs (Nonempty Unit)
  | n + 1 => @instNonemptyProd (BernoulliCube n) Bool (bernoulliCubeNonempty n) inferInstance

                                                                                     
                                                             
             
               
                                                                   
                                                                     
                                      

                                                                                
                                                             
                                                                             
                  
           
                                                                 
                                                      
                
                                                                      
                                                                                   
                                                                                   
                                         

end
end GinibrePoincare
