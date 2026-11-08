/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.CatalystInsertionTraceStage89

/-! # The configuration after all insertions: tokens, carriers, separation

After every active vertex has been processed, the tokens are
`inl e` (`e ∈ Y`, original) and `inr (y, i)` (`y ∈ A`, `i : Fin 3`,
catalytic), with current positions `tokPos`. We prove:

* `tokPos` is injective on the tokens and its image is the configuration;
* at the carrier `cz y` sit exactly the original token `y – nm y` and the
  catalytic token `(y, 0)`; at `cz' y` exactly `y – np y` and `(y, 1)`;
* at the catalytic vertex `cs y` sit exactly `(y, 0)`, `(y, 2)`; at `ct y`
  exactly `(y, 1)`, `(y, 2)`; no token sits at any other vertex;
* hence the configuration is 2-regular on carriers ∪ catalytic vertices and
  every other vertex (all original active vertices and all centres `co y`)
  is isolated;
* separation: every catalytic edge has a catalytic endpoint, and each
  catalytic vertex is adjacent to at most one carrier.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.CatalystInsertionStage89

open Finset AntiEdgeSelection TypedTransformer CatalystSelectionStage89

variable {V : Type*} [DecidableEq V] {t : ℕ}

namespace Data

variable (S : Data V) (cz cz' : V → V) (P : Finset V)

/-- Tokens: original `inl e` for `e ∈ Y`, catalytic `inr (y, i)` for `y ∈ A`. -/
def tokens : Finset (Sym2 V ⊕ (V × Fin 3)) := S.Y.disjSum (S.A ×ˢ univ)

                                       
                                          
                               
                                       

                                                  
                                                    
                                                  

                    
def carriers : Finset V := S.A.image cz ∪ S.A.image cz'

                              
                                                           

                                                                                      
       
                                                                                             
                                    
             
                                             
                                                 
                                                                   
                                                              
                                 
                                  

                                                     
                                                                            
                                        

                                  
                                                         
                                                           
                                                               
                       

end Data

section carriers

variable {S : Data V} {Z₀ : Finset V} {cz cz' : V → V}

                       
                                                                                      
                                     
               
                                    

                       
                                                                                       
                                       
               
                                      

                       
                                                                                            
                       
                     
                             
                                    

theorem rep_full {u : V} (hu : u ∈ S.A) (e : Sym2 V) :
    S.rep cz cz' S.A u e = if e = s(u, S.nm u) then cz u else cz' u := by
  simp [Data.rep, hu]

theorem catTok_full {y : V} (hy : y ∈ S.A) :
    S.catTok cz cz' S.A y 0 = s(cz y, S.cs y) ∧ S.catTok cz cz' S.A y 1 = s(cz' y, S.ct y) ∧
      S.catTok cz cz' S.A y 2 = s(S.cs y, S.ct y) := by
  simp [Data.catTok, hy]

                                                                    
                                 
                                                                              
                                                 
                                        

                       
                                                                                                
                                 

                       
                                            
                                                                   
                                 

                                                           
                                                          
                                           
                                             
     

                                                                  
                                                               
                                               
                                             
     

end carriers

variable [Fintype V]

section

variable {p : V → Fin t} {F : Finset (Multiset (Fin t))} {G : SimpleGraph V}
  [DecidableRel G.Adj] {B : Finset (Sym2 V)} {S : Data V} {Z₀ : Finset V}
  {cz cz' : V → V}

                                                                                  
                                         
               
                                                                              
                                                                                         
                                                         

                                                                                  
                                         
               
                                                                              
                                                                                         
                                                         

                                                                                       
                          
                     
                                         
             
                                                                                
                                                                                             
                                                         

                                                         
                                                                                         
                                     
                                                                             
                                      
                                  
                                                                          
                         

                                                                                
                                                                            
                                                                      
                        
               

                                                                   
                                     
         
                                              
                                 
                                

                                                                              
theorem curY_carrier (fr : Frame p F G B S Z₀) {e : Sym2 V} (he : e ∈ S.Y) {v : V}
    (hv : v ∈ S.curY cz cz' S.A e) : ∃ u ∈ S.A, v = cz u ∨ v = cz' u := by
  obtain ⟨u, hu, hr⟩ := (S.mem_curY cz cz' S.A).mp hv
  have huA := fr.supp e he u hu
  refine ⟨u, huA, ?_⟩
  rw [rep_full huA] at hr
  split_ifs at hr
  · exact Or.inl hr.symm
  · exact Or.inr hr.symm

theorem curY_notZ (fr : Frame p F G B S Z₀) (hc : Carriers Z₀ cz cz' S.A) {e : Sym2 V}
    (he : e ∈ S.Y) {v : V} (hv : v ∈ S.curY cz cz' S.A e) : v ∉ Z₀ := by
  obtain ⟨u, hu, h | h⟩ := curY_carrier fr he hv <;> rw [h]
  · exact (hc.fresh u hu).1
  · exact (hc.fresh u hu).2

                                                                                   
                                                
                                                       
             
            
                                                       
                                 
                           
                          
                                           
                                                
              
                                                                                          

                                                                                    
                                                
                                                        
             
            
                                                       
                                 
                           
                          
                                           
                                     
               
                                                    
              
                                                                  
                                              

                                                                     
                                      
                                                                                
                                                                                       
       
                           
                      
                                                                                
               
                     
                                           
                
                                                                               
                      
                                                                                
                    
               
                      
                                            
                                                                                            
                                             
                           
                                            
                             
                           
                             
                       
                                                                         

                                                                      
                                      
                                                                                 
                                                                                        
       
                           
                      
                                                                                
               
                     
                                            
                
                                                                                
                      
                                                                                
                    
               
                      
                                            
                                                                                            
                                                 
                               
                                              
                               
                               
                               
                       
                                                                                  

                                                                       
                                         
                                                                                
                                                                                   
       
                           
                      
                                                                                    
               
                                                   
                      
                                                                       
               
                      
                                            
                                                                                            
                                
                                                    
                                    
                                           
                                                    
                                           
                                      
                                                                           
                                                                                    

                                                                       
                                         
                                                                                
                                                                                   
       
                           
                      
                                                                                    
               
                                                   
                      
                                                                       
               
                      
                                            
                                                                                            
                                  
                                                
                                    
                                                    
                                                
                                                    
                                      
                                                                                    
                                                                                    

                                        
                                                     
                                                                               
                                                                                     
                  
                                 
       
                                     
                           
                      
                   
                                                  
                          
                          
                      
                    
                                                                                    
                            
                            
                            
                            
                            
                            

                                                                      
theorem inl_ne_inr (fr : Frame p F G B S Z₀) (hc : Carriers Z₀ cz cz' S.A) {e : Sym2 V}
    (he : e ∈ S.Y) {y : V} (hy : y ∈ S.A) (i : Fin 3) :
    S.curY cz cz' S.A e ≠ S.catTok cz cz' S.A y i := by
  intro h
  obtain ⟨-, hcs, hct⟩ := fr.mem_cat hy
  obtain ⟨h0, h1, h2⟩ := catTok_full (cz := cz) (cz' := cz') hy
  fin_cases i
  · exact curY_notZ fr hc he (h ▸ h0 ▸ Sym2.mem_mk_right _ _) hcs
  · exact curY_notZ fr hc he (h ▸ h1 ▸ Sym2.mem_mk_right _ _) hct
  · exact curY_notZ fr hc he (h ▸ h2 ▸ Sym2.mem_mk_left _ _) hcs

                                                                      
                                                                              
                                                  
                       
                                                                            
             
                                      
                          
                          
                                                 
                                   
              
                                                               
                                                                                  
                                                                
                             
                                                         
                      
                                                          
                                          
                            
                                                                                
                                     
                                                   
                                
              
                                 
                                                                                 
                                      
                                                   
                                
                                                                         
                                 
                                                   
                                                                                         
                                                  
               
                                                      
                                                        
                                  
                                  
                                                    
                              
                  
           
                                                       
                                                        
                                   
                                  
                                                    
                              
                  
           
                                                        
                                                        
                                  
                                  
                                                    
                              
                  
           

                                                              
                                                                             
                                                              
                                                                                  
                                                                          

                                                                                   
                                                                                       
                                                                            
                     
                                         
                                                                           

                                                                        
                                                                               
                                                                                      
                                                                                      
                                                                                            
                          
                                                                        
                                                                       
                                                                              
                                               
                                                
                                               
                                               

                                                                                           
                                                                                             
                                                   
                                              
                                              

                                                    
                                                                                             
                                                  
                    
                
                                                                           
                        
                                               
                               
                               
                                            
                              
                              

                                                                          
                                                                                          
                                                               
                                                           
                                                                 
                                               
                        
                                                                           
                                                                                  
                                
                                
                             
                             
                                                          
                                                           
                
                                         
                                                      
                
                       
             
                                                          
                                       
                                                                                   
                                                                              
                                                                        

                   
                                                                                     
                                                                    
                                                                  
                                                                                   
                                                                                   
             
                                                          
                                                          
                                                      

                                                                         
                                                                                      
                                                       
                                                                
                                              
                              
                                                  
                                                                       
                               
                         
                                                         
                                              
                             
                             
                                                              
                                              
                           
                                   
                   
                                                   
                                                   
                  
                                   
                   
                                                   
                                                
                                                

                                                                          
                                                                                      
                                                       
                                                                 
                                              
                              
                                                  
                                                                       
                               
                         
                                                         
                                              
                             
                             
                                                              
                                              
                           
                                   
                   
                                                   
                                                       
                  
                                   
                   
                                                   
                                        
                                                

                                                                                     
                                                                                             
                            
                                                                                      
                                                        
                                            
                                                          
              
                                         
                                                             
                                                           
              
                                         
                                                             

end

end PartitionedTriangleAbsorption.CatalystInsertionStage89
