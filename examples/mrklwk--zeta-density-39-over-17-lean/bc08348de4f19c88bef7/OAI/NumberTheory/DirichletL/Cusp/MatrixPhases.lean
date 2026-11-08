module
public import OAI.NumberTheory.DirichletL.ChineseRemainder.AdditiveCharacters
public import OAI.NumberTheory.DirichletL.Arithmetic.EisensteinIdeals
public import Mathlib
@[expose] public section

namespace OAI

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
noncomputable section

namespace ShortDraftCusp

variable {R : Type*} [CommRing R]

                                                       
                                                       
                                                

                                         
                                                
              

                                                         
          

                                                        
                                                
                            
                                                      
         

                               
                                 
                            
          

                                                               
                                                   
                
         
                        

                                       
                                                 
                
         
      

                                              
                              
                                            
                                                      
         
         
         
                                        
         
                           

                                               
                              
                                            
                                                                      
         
         
         
                                        
         
                           

                                                 
                              
                                            
                                                                        
         
         
         
                                                 
         
                           

end ShortDraftCusp

namespace ShortDraftConcretePhase
open ShortDraftTrace

                                                                
                                      
                                                           
                                                                 
                                          
                                                             
                                                                               
                               
                                                                
               
          
             
                                                              
                      
           
            
                       
                                  
               

end ShortDraftConcretePhase

namespace ShortDraftGauss

open Complex
open scoped ComplexConjugate

variable {F : Type*} [Field F] [Fintype F]

                                                                      
                                       
                                                     
                       
                                                      
                                                 
                                
                                            
                                                   
                                  
        
                                                         
                                                  
                                       
                                                    
                                                        
                                  
                                                              

                                                                    
                                       
                                                                       
                                             
                                                     
                                                
                                    
                                                              
                                                                             
                             

end ShortDraftGauss

namespace EisensteinRayPhase

abbrev SquareClass := ZMod 2 × ZMod 2

def R (a b : SquareClass) : ℤ :=
  (-1) ^ (a.1.val * b.2.val + a.2.val * b.1.val + a.2.val * b.2.val)

                                                             
                

                                                                            
                

                                                                             
                

                                                                 
                

end EisensteinRayPhase

namespace ShortDraftSextic
open scoped Classical
variable {R : Type*} [CommRing R]

                                                   
                              
                                               
           
                                                              
                        
                                
             

end ShortDraftSextic

namespace ShortDraftGaussJacobi
open Finset

variable {F : Type*} [Field F] [Fintype F]

                                               
                                       
                                            
           
                                   
                                       
                      
                          
            
                                                  
                                          
         
      
                                                         
                                              
                                          
                         
                                
               
                           
          
                                                                     

                                                         
                                           
                                   
                                       
                               
                         
                       
                                            

                                              
                            
                                       
                                                                  
                       
           
                      
                            
           
                                 
                         
                                       
                     
                  
                                                   

                                                            
                                                   
                                                                 
                       
           
                      
                            
           
                                 
                         
                                       
                     
                  
                           
                                                                
                                                      
                                           
                                                            
                                                  
                          
      
                                                                              
                                                                         
                                                                       

                                                                       
                                                   
                                                               
                                                                
                                             
                                                                             
                       
             
                                              
                                               
             
                                        
                                                     
            
                                                      
      

end ShortDraftGaussJacobi

namespace ShortDraftQuadraticGauss
open Finset
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

                                                         
                                           
                                                                    
                              
                                      
                                                              
                                                 
                                                              
                              
             
                                                                
                                                       
                                              
                                                                      
                 
          
               
                       
                                           
                                         
                                                   
             
                           
                             
                                                                     
                                      
     

end ShortDraftQuadraticGauss

namespace ShortDraftQuotientPhase
variable {A B : Type*} [CommGroup A] [CommGroup B]

                                                  
                                                    
                                  
                            
                                  
                                                  
                     
               
                                                     
                                                  
                             
                                   
                                       
                                   
                                       
                                                 
              
                                      
                                     
                                               
                                             
                         
                                             
                                        
                                       
                                      
                                     
                                  
                                           
        
                                                 
                                                   
                                                   
        

end ShortDraftQuotientPhase

namespace EisensteinEPrimaryPhase

abbrev Coord := ZMod 4 × ZMod 4
                    

def mul (x y : Coord) : Coord :=
  (x.1 * y.1 - x.2 * y.2,
   x.1 * y.2 + x.2 * y.1 - x.2 * y.2)

def odd (x : Coord) : Prop := x.1.val % 2 = 1 ∨ x.2.val % 2 = 1

instance : DecidablePred odd := fun x =>
  inferInstanceAs (Decidable (x.1.val % 2 = 1 ∨ x.2.val % 2 = 1))

                              
                                                   
                                           

def norm (x : Coord) : ZMod 4 :=
  x.1 * x.1 - x.1 * x.2 + x.2 * x.2

def ePrimary (x : Coord) : Prop :=
  let cube := mul (mul x x) x
  cube.1 - 2 * cube.2 = 1

instance : DecidablePred ePrimary := fun x =>
  inferInstanceAs (Decidable ((mul (mul x x) x).1 -
    2 * (mul (mul x x) x).2 = 1))

                                                     
                                                                        
                

                                                               
                             
                                                               
                         
                

                                                                   
                                                    
                

                                                               
                                                                   
                

                                                            
                                                            
                                                          

                                                               
                                                 
                

                                                                             
                

                                                          
                                          
                

end EisensteinEPrimaryPhase

namespace ShortDraftGaussianPhaseTable
abbrev SquareClass := ZMod 2 × ZMod 2

                                       
                                                 

                                               
                                                                                

                                           
                                                             
                

end ShortDraftGaussianPhaseTable

namespace ActualEisensteinCoordinates
abbrev K := CyclotomicField 3 ℚ
abbrev O := NumberField.RingOfIntegers K
instance : IsCyclotomicExtension {3} ℚ K := CyclotomicField.isCyclotomicExtension 3 ℚ
theorem hζ : IsPrimitiveRoot (IsCyclotomicExtension.zeta 3 ℚ K) 3 :=
  IsCyclotomicExtension.zeta_spec 3 ℚ K
def omega : O := hζ.toInteger
def pb : PowerBasis ℤ O := hζ.integralPowerBasis

private theorem pb_dim : pb.dim = 2 := by
  simp [pb, Nat.totient_prime Nat.prime_three]

theorem pb_gen : pb.gen = omega := by
  exact hζ.integralPowerBasis_gen

theorem exists_coordinates (x : O) :
    ∃ a b : ℤ, x = (a : O) + (b : O) * omega := by
  let i0 : Fin pb.dim := ⟨0, by rw [pb_dim]; decide⟩
  let i1 : Fin pb.dim := ⟨1, by rw [pb_dim]; decide⟩
  let a : ℤ := (pb.basis.repr x) i0
  let b : ℤ := (pb.basis.repr x) i1
  refine ⟨a, b, ?_⟩
  have hsum := pb.basis.sum_repr x
  have huniv : (Finset.univ : Finset (Fin pb.dim)) = {i0, i1} := by
    ext i
    have hi : i.val < 2 := by simpa only [pb_dim] using i.isLt
    have hv : i.val = 0 ∨ i.val = 1 := by omega
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    rcases hv with h | h
    · left; exact Fin.ext h
    · right; exact Fin.ext h
  rw [huniv] at hsum
  have hne : i0 ≠ i1 := by decide
  have hnot : i0 ∉ ({i1} : Finset (Fin pb.dim)) := by
    simpa only [Finset.mem_singleton] using hne
  rw [Finset.sum_insert hnot, Finset.sum_singleton] at hsum
  simp only [pb.basis_eq_pow] at hsum
  have hi0 : (i0 : ℕ) = 0 := rfl
  have hi1 : (i1 : ℕ) = 1 := rfl
  simpa [a, b, hi0, hi1, pb_gen, smul_eq_mul, mul_comm] using hsum.symm

def i0 : Fin pb.dim := ⟨0, by rw [pb_dim]; decide⟩
def i1 : Fin pb.dim := ⟨1, by rw [pb_dim]; decide⟩

def eval (a b : ℤ) : O := (a : O) + (b : O) * omega

private theorem eval_basis (a b : ℤ) :
    eval a b = a • pb.basis i0 + b • pb.basis i1 := by
  simp [eval, PowerBasis.basis_eq_pow, i0, i1, pb_gen, mul_comm]

theorem unique_coordinates {a b c d : ℤ}
    (h : eval a b = eval c d) : a = c ∧ b = d := by
  have h0 := congrArg (fun x : O => (pb.basis.repr x) i0) h
  have h1 := congrArg (fun x : O => (pb.basis.repr x) i1) h
  have hne : i0 ≠ i1 := by decide
  rw [eval_basis, eval_basis] at h0 h1
  constructor
  · simpa only [map_add, map_smul, pb.basis.repr_self, Finsupp.add_apply,
      Finsupp.smul_apply, Finsupp.single_apply, ite_eq_left, ite_eq_right hne.symm,
      smul_eq_mul, mul_one, mul_zero, add_zero] using h0
  · simpa only [map_add, map_smul, pb.basis.repr_self, Finsupp.add_apply,
      Finsupp.smul_apply, Finsupp.single_apply, ite_eq_left, ite_eq_right hne,
      smul_eq_mul, mul_one, mul_zero, zero_add] using h1

private theorem omega_sq : omega ^ 2 = -omega - 1 := by
  simpa [omega] using IsCyclotomicExtension.Rat.Three.eta_sq hζ

                                                 
                                           
                                                     
      
                                                
                       
          
                                   
                      
               
          

theorem eval_mul (a b c d : ℤ) :
    eval a b * eval c d = eval (a*c-b*d) (a*d+b*c-b*d) := by
  simp only [eval]
  calc
    ((a : O) + (b : O) * omega) * ((c : O) + (d : O) * omega)
      = (a : O) * c + ((a : O) * d + (b : O) * c) * omega +
          ((b : O) * d) * omega ^ 2 := by ring
    _ = ((a*c-b*d : ℤ) : O) + ((a*d+b*c-b*d : ℤ) : O) * omega := by
          rw [omega_sq]
          push_cast
          ring

                                         
                                                     
                                              
                                                                                    
                                                                                    
                       
                       
                                        
              
                                                           
           
      

theorem exists_pair (x : O) :
    ∃ p : ℤ × ℤ, eval p.1 p.2 = x := by
  obtain ⟨a, b, h⟩ := exists_coordinates x
  exact ⟨(a, b), h.symm⟩

def coords (x : O) : ℤ × ℤ := Classical.choose (exists_pair x)

theorem eval_coords (x : O) : eval (coords x).1 (coords x).2 = x :=
  Classical.choose_spec (exists_pair x)

                                                      
                              

                                
                                                           
                                                       
                                                           
                                              

                               
                                                                             
      
                                                             
                                                                           
                                                                 
                                 
                                                 

                                 
                                                                             
                                       

                                              
                                                          
                                     
                           
                             
                             

def lift (v : EisensteinEPrimaryPhase.Coord) : O :=
  eval (v.1.val : ℤ) (v.2.val : ℤ)

                                                          
                              
                           

                                           
                                                    
                                                    
                                                                      
                                 
                                                             
                           
                                    
                                                               
              

                                   
                                               
                                                    
                                    
                                                                              
                                                 
                                                                       

                               
                                               
                                                    
                                
                                                                  
                                    
                                                 
                                                                   

                                                            
                                               
                        
          

                                                                     
                                 
                                                  
                

                                                                     
                                           
                                  
                                        
                

                                             
                                                                 
             
                 
                          
                                           
                                        
              
                  
                                                         
                                                
                                                                     
                                                
                                                                     
                                                                                
                                                                                
              
                         
                        
                
                 
             
        
                                                                                  
                                          

                             
                                               
                                               
                
                  
                                            
                                            
                                            

                                                                                         
                                                                    

                                                                                                          
                                             
                

                                     
                                                                         
                                                                    
                

                                      
                                                                         
                                                                    
                

                                                                  

                                                                     
                            

                                     
                                               
                                                        
                 
                            
                                   

                                      
                                               
                                                        
                 
                            
                                    
end ActualEisensteinCoordinates

end

end OAI
