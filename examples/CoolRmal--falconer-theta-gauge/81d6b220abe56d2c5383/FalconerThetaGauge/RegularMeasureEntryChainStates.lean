/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FalconerThetaGauge.RegularMeasureEntryTestLists
public import Mathlib
/-!
# Concrete combinatorial states of the energy induction

Fourier states use the actual scheduled list of their base interval, retaining
exactly the tests whose anchors have not yet been reached. The six transition
constructors are the child types of Table 1 in the manuscript.
-/

@[expose] public section

noncomputable section

open Finset
open scoped Classical

namespace FalconerThetaGauge

/-- The actual tests still present at start depth `a` in a Fourier state. -/
def profileRemainingTests (A : ℕ → ℝ) (q N b e a : ℕ) : Finset ProfileScheduleTest :=
  (profileScheduledTests A q N b e).filter (fun test ↦ a < test.anchor)

/-- The length of the longest remaining test, with value zero for the empty list. -/
def profileLongestTestLength (A : ℕ → ℝ) (q N b e a : ℕ) : ℕ :=
  (profileRemainingTests A q N b e a).sup ProfileScheduleTest.length

                                                                      
                   
                                                                               
                  
                                                       
                                                           

                                                                         
                   
                                                                                  
                                                            

                                                                     
                                                     
                                               
                                                              
                                                               
               
                                                        
                                                                        
                            
         
                              
                                                                    
                                
                               

                                                                             
inductive ProfileChainState
  | discrepancy (start finish : ℕ)
  | fourier (baseStart baseFinish start finish : ℕ)
  deriving DecidableEq

def ProfileChainState.start : ProfileChainState → ℕ
  | .discrepancy a _ => a
  | .fourier _ _ a _ => a

def ProfileChainState.finish : ProfileChainState → ℕ
  | .discrepancy _ t => t
  | .fourier _ _ _ v => v

                                                          
                             
                            

                                                                   
def ProfileChainState.Valid (N δ : ℕ) : ProfileChainState → Prop
  | .discrepancy a t => a ≤ t ∧ t ≤ N
  | .fourier b e a v => b ≤ a ∧ a ≤ v ∧ v ≤ e ∧ e ≤ N ∧ e ≤ v + δ

/-- The six child types of the four moves, with their concrete intervals and masks. -/
inductive ProfileChainMove (A : ℕ → ℝ) (q N δ : ℕ) :
    ProfileChainState → ProfileChainState → Type
  | linearize (a t : ℕ) (hlong : 100 * q < t - a)
      (hright : a + t < 2 * profileSplitPoint A q N a t) :
      ProfileChainMove A q N δ (.discrepancy a t)
        (.discrepancy a (profileSplitPoint A q N a t))
  | lowFrequency (a t : ℕ) (hlong : 100 * q < t - a)
      (hleft : 2 * profileSplitPoint A q N a t ≤ a + t) :
      ProfileChainMove A q N δ (.discrepancy a t) (.discrepancy a (t - δ))
  | highFrequency (a t v : ℕ) (hlong : 100 * q < t - a)
      (hleft : 2 * profileSplitPoint A q N a t ≤ a + t)
      (hvlo : t - δ < v) (hvhi : v ≤ t) :
      ProfileChainMove A q N δ (.discrepancy a t)
        (.fourier a t (profileSplitPoint A q N a t) v)
  | refine (b e a v : ℕ) (hlong : 100 * q < v - a) (test : ProfileScheduleTest)
      (htest : test ∈ profileRemainingTests A q N b e a)
      (hlargest : test.length = profileLongestTestLength A q N b e a)
      (hlarge : v - a ≤ 2 * test.length) :
      ProfileChainMove A q N δ (.fourier b e a v) (.fourier b e test.anchor v)
  | near (b e a v : ℕ) (hlong : 100 * q < v - a)
      (hsmall : 2 * profileLongestTestLength A q N b e a < v - a) :
      ProfileChainMove A q N δ (.fourier b e a v)
        (.fourier b e (v - 2 * max (profileLongestTestLength A q N b e a) δ) v)
  | far (b e a v n : ℕ) (hlong : 100 * q < v - a)
      (hsmall : 2 * profileLongestTestLength A q N b e a < v - a)
      (hnlo : a < n)
      (hnhi : n < v - 2 * max (profileLongestTestLength A q N b e a) δ + 12)
      (hnv : n ≤ v) :
      ProfileChainMove A q N δ (.fourier b e a v) (.discrepancy n v)

                                                                                             
                                                                            
                                    
                      
                         
                          
                   
                 
                

                                           
                                                                               
                                                                              
                           

                                                                                           
                                                             
                                                        
                                                              
                                                               
                 
                                 
                          
                                                            
                                                      
                                                               
                                   
                          
                                                    
         
                                                
                          
                                                            
                                                    
                                                                         
                               
         
                                                      
                                          
                                                         
                                                                   
                                                                        
                               
         
                                
                                          
                                                                              
           
                                                                             
                                                                
                                                                
                               
         
                                               
                                          
                                        
         

end FalconerThetaGauge
