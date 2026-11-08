module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Data.Real.Sqrt
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import Mathlib.Tactic

/-!
# The weighted shift (Section 4 of the paper, Definition 4.1 and Lemma 4.2)

On `ℋ = ℓ²(ℕ₀)` with orthonormal basis `(e_n)`, the weighted shift is
`S_N e_0 = √2 e_1`, `S_N e_n = e_{n+1}` (`n ≥ 1`), and `D_N = 2 P_0 - P_1`.
-/

@[expose] public section

open scoped ComplexConjugate

noncomputable section

namespace PolyaNeumann

/-- The Hilbert space `ℋ = ℓ²(ℕ₀)`. -/
abbrev Ell2 := lp (fun _ : ℕ => ℂ) 2

/-! ### Instance normalisation for the Lean/Mathlib `v4.35.0-rc2` port

With Lean/Mathlib `v4.35.0-rc2`, type-class search elaborates the additive and module
structures of the `lp` model of `ℋ` through the subtype (`AddSubmonoidClass`) path, and the
stricter transparency discipline of the new unifier then no longer identifies these with the
structures expected by generic lemmas such as `add_smul` or by instances on `ℋ →L[ℂ] ℋ`.
The instances below fix one canonical choice: each is the standard Mathlib instance (all are
definitionally equal to the previously inferred ones), registered with high priority so that
every statement is elaborated with it.  They change no definition or statement of the
development. -/

instance (priority := high) instIsTopologicalAddGroupComplex : IsTopologicalAddGroup ℂ :=
  SeminormedAddCommGroup.toIsTopologicalAddGroup

instance (priority := high) instAddCommGroupEll2 : AddCommGroup Ell2 :=
  NormedAddCommGroup.toAddCommGroup

instance (priority := high) instAddCommMonoidEll2 : AddCommMonoid Ell2 :=
  AddCommGroup.toAddCommMonoid

instance (priority := high) instModuleComplexEll2 : Module ℂ Ell2 :=
  NormedSpace.toModule

instance (priority := high) instModuleRealEll2 : Module ℝ Ell2 :=
  NormedSpace.toModule

instance (priority := high) instIsTopologicalAddGroupEll2 : IsTopologicalAddGroup Ell2 :=
  SeminormedAddCommGroup.toIsTopologicalAddGroup

instance : ContinuousStar (Ell2 →L[ℂ] Ell2) :=
  @NormedStarGroup.to_continuousStar (Ell2 →L[ℂ] Ell2) _ _ _

instance : StarModule ℝ (Ell2 →L[ℂ] Ell2) :=
  @StarModule.complexToReal (Ell2 →L[ℂ] Ell2) _ _ _ _

instance : IsScalarTower ℝ (Ell2 →L[ℂ] Ell2) (Ell2 →L[ℂ] Ell2) :=
  @IsScalarTower.right ℝ (Ell2 →L[ℂ] Ell2) _ _ _

instance : SMulCommClass ℝ (Ell2 →L[ℂ] Ell2) (Ell2 →L[ℂ] Ell2) :=
  @Algebra.to_smulCommClass ℝ (Ell2 →L[ℂ] Ell2) _ _ _

                                                            
                                                                            
                             

                                                                    
                                                                                      
                             

                                                                   
                                                                     

                                                                           
                                        

                                                                    
                                        

                                    
                                                                
                               
                                                                     
        

                              
                                
          
                                

                                
                                                                         

                                                      

                                                                          
                                                   
                               

                                                                          
                   
                              
                            

                                                                               
                                                   
                                               
                 

                                         
                                                                       
                        
                                                                             

                                            
                                                                                   
                        
                                                                             

                                                                               
                               
                                                                        
                                
                          

                                                                                     
                                                                                           
                                                               

                             
                                    
                                                                     
                    
                          
                                                                
                                        
                     
                          
                                                    
                                     

                               
                                       
                                                                           
                    
                          
                                                                         
                               
                     
                          
                                                          
                            

                                                                          
                                                                
                                       
                                                                                 
                                     
                                             
                                                                                
                       
                                                                                   
                                                           
                                                              
                                      
                   

                                                                                
                                                                
                                       
                                                                                 
                                        
                                                                           
                                                                                       
                                                                     
                                           
                                                        
                                                 

                                                                                     
                                                                                    

                                        
                                                                                             

                                                                            

                                                    
                                                                     

                                                  
                                                                        

                                                         
                                                                                 
                                         
           
                                                                               
                                  
                                                              
                                                                   
                       
                         
                   
                                      

                                                                             
                      
                              
                                                                                       
                                                  
                                                                               
                                                

                                     
                                                                         

                                       
                                                                  
                                         
        
                                          

                                      
                                                           
                                                                                  
                                                                      
                                                                                         
                                              
                                  

                                       
                          
                                                                                             
                   
                             
        
                        
                                                                                        
                                                                  
                         
                                                       
                                                             
                                                                                             
                                                             
                                                                                   

                                          
                                                
                                                                        

                                    
                           
                                                                  

                                 
                           
                                                             

                                 
                                                               
                                                                          
                                                              
                                                        
                                                                                                  
                                

                                 
                                                               
                                                                          
                                                                            
                                                                                   
                                                           

                                           
                                                                            
                         
        
                                                                                  
                                                                                              
        

                                                   
                                                    

                                                                                  
                        
                  
                                                                                  
                    
                 
            

                                                  
                                                                               
                                                                           
           
                                                                       
                  
                                
                              
              
                                                                     
                                

                                                                                          
                                                                                        
                             
                                                       
                                
                              
              
                                                                     
                                

end PolyaNeumann

end
