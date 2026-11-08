module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import CookMagyar.LocalFactorTail
public import CookMagyar.LocalLargePrimeCounts
public import Mathlib.Logic.Equiv.Fin.Basic

@[expose] public section

open scoped BigOperators

namespace SystolicGrowth
namespace CookMagyarPrimePower

/-! # Prime-power stationary-phase algebra

This file develops the finite algebra behind the prime-power tail of the
Cook--Magyar singular series.  The central reindexing writes a residue
modulo `M * R` uniquely as `x + M*y`, with `x` modulo `M` and `y` modulo
`R`.  For `M = p^m`, `R = p^d`, and `d ≤ m`, the quadratic Taylor
remainder of `X³-X` vanishes modulo `p^(m+d)`.  Orthogonality in `y`
then restricts the outer sum to residues for which the derivative vanishes
modulo `p^d`.
-/

open CookMagyarFiniteFourier CookMagyarLocal

/-- The additive embedding `y ↦ M*y` from residues modulo `R` into
residues modulo `M*R`. -/
def blockKernelAddHom (M R : ℕ) [NeZero M] [NeZero R] :
    ZMod R →+ ZMod (M * R) where
  toFun y := (M * y.val : ℕ)
  map_zero' := by simp
  map_add' a b := by
    rw [← Nat.cast_add]
    apply (ZMod.natCast_eq_natCast_iff _ _ (M * R)).2
    have h : (a + b).val ≡ a.val + b.val [MOD R] := by
      apply (ZMod.natCast_eq_natCast_iff _ _ R).mp
      simp
    simpa [Nat.mul_add, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
      h.mul_left' M

@[simp] theorem blockKernelAddHom_apply (M R : ℕ) [NeZero M] [NeZero R]
    (y : ZMod R) :
    blockKernelAddHom M R y = (M * y.val : ℕ) := rfl

/-- Every residue modulo `M*R` is uniquely a low digit modulo `M` plus
`M` times a high digit modulo `R`. -/
noncomputable def residueBlockEquiv (M R : ℕ) [NeZero M] [NeZero R] :
    ZMod M × ZMod R ≃ ZMod (M * R) :=
  ((ZMod.finEquiv M).symm.toEquiv.prodCongr
      (ZMod.finEquiv R).symm.toEquiv).trans <|
    Equiv.prodComm _ _ |>.trans <|
      finProdFinEquiv |>.trans (finCongr (Nat.mul_comm R M)) |>.trans
        (ZMod.finEquiv (M * R)).toEquiv

@[simp] theorem residueBlockEquiv_apply (M R : ℕ) [NeZero M] [NeZero R]
    (x : ZMod M) (y : ZMod R) :
    residueBlockEquiv M R (x, y) =
      (x.val + M * y.val : ℕ) := by
  have hsum : x.val + M * y.val < M * R := by
    calc
      x.val + M * y.val < M + M * y.val :=
        Nat.add_lt_add_right x.val_lt _
      _ = M * (y.val + 1) := by ring
      _ ≤ M * R := Nat.mul_le_mul_left M (Nat.succ_le_iff.mpr y.val_lt)
  apply ZMod.val_injective (M * R)
  rw [ZMod.val_cast_of_lt hsum]
  cases M with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ M =>
      cases R with
      | zero => exact (NeZero.ne 0 rfl).elim
      | succ R => rfl

                                                                        
                                                         
                                           

                                                
                                   
                               
                                                               
                              
                       
                                                                
           
                                                                   

                                               
theorem blockKernelAddHom_injective (M R : ℕ) [NeZero M] [NeZero R] :
    Function.Injective (blockKernelAddHom M R) := by
  intro a b hab
  have hmod : M * a.val ≡ M * b.val [MOD M * R] := by
    apply (ZMod.natCast_eq_natCast_iff _ _ (M * R)).mp
    exact hab
  have hM : 0 < M := NeZero.pos M
  have ha_lt : M * a.val < M * R :=
    Nat.mul_lt_mul_of_pos_left a.val_lt hM
  have hb_lt : M * b.val < M * R :=
    Nat.mul_lt_mul_of_pos_left b.val_lt hM
  unfold Nat.ModEq at hmod
  rw [Nat.mod_eq_of_lt ha_lt, Nat.mod_eq_of_lt hb_lt] at hmod
  exact ZMod.val_injective R (Nat.eq_of_mul_eq_mul_left hM hmod)

/-- Multiplication by `M` depends only on reduction modulo `R` when the
ambient modulus is `M*R`. -/
theorem blockKernel_cast_eq_mul (M R : ℕ) [NeZero M] [NeZero R]
    (D : ZMod (M * R)) :
    blockKernelAddHom M R (D.cast : ZMod R) =
      (M : ZMod (M * R)) * D := by
  rw [← ZMod.natCast_zmod_val D]
  rw [blockKernelAddHom_apply]
  push_cast
  rw [← Nat.cast_mul, ← Nat.cast_mul]
  apply (ZMod.natCast_eq_natCast_iff _ _ (M * R)).2
  have hcast : ((D.cast : ZMod R).val : ZMod R) = (D.val : ZMod R) := by
    rw [ZMod.natCast_zmod_val]
    exact ZMod.cast_eq_val D
  have hmod : (D.cast : ZMod R).val ≡ D.val [MOD R] :=
    (ZMod.natCast_eq_natCast_iff _ _ R).mp hcast
  simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
    hmod.mul_left' M

/-- Multiplication by `M` vanishes modulo `M*R` exactly when the other
factor vanishes after reduction modulo `R`. -/
theorem natCast_mul_eq_zero_iff_cast_eq_zero
    (M R : ℕ) [NeZero M] [NeZero R] (D : ZMod (M * R)) :
    (M : ZMod (M * R)) * D = 0 ↔ (D.cast : ZMod R) = 0 := by
  rw [← blockKernel_cast_eq_mul M R D]
  constructor
  · intro h
    apply blockKernelAddHom_injective M R
    simpa using h
  · intro h
    simp [h]

/-- The character in the high block produced by a fixed linear
coefficient. -/
noncomputable def blockLinearCharacter
    (M R : ℕ) [NeZero M] [NeZero R] (D : ZMod (M * R)) :
    AddChar (ZMod R) ℂ :=
  (standardAdditiveCharacter (q := M * R)).compAddMonoidHom
    ((AddMonoidHom.mulRight D).comp (blockKernelAddHom M R))

@[simp] theorem blockLinearCharacter_apply
    (M R : ℕ) [NeZero M] [NeZero R]
    (D : ZMod (M * R)) (y : ZMod R) :
    blockLinearCharacter M R D y =
      standardAdditiveCharacter
        (blockKernelAddHom M R y * D) := rfl

/-- Exact block orthogonality.  This is the stationary-phase cancellation:
the inner block sum vanishes unless the linear coefficient is zero modulo
the block modulus. -/
theorem sum_blockLinearCharacter
    (M R : ℕ) [NeZero M] [NeZero R] (D : ZMod (M * R)) :
    (∑ y : ZMod R, blockLinearCharacter M R D y) =
      if (D.cast : ZMod R) = 0 then (R : ℂ) else 0 := by
  by_cases hD : (D.cast : ZMod R) = 0
  · rw [if_pos hD]
    have hmul : (M : ZMod (M * R)) * D = 0 :=
      (natCast_mul_eq_zero_iff_cast_eq_zero M R D).2 hD
    calc
      (∑ y : ZMod R, blockLinearCharacter M R D y) =
          ∑ _y : ZMod R, (1 : ℂ) := by
            apply Finset.sum_congr rfl
            intro y _hy
            rw [blockLinearCharacter_apply]
            have hy : blockKernelAddHom M R y * D = 0 := by
              rw [blockKernelAddHom_apply, Nat.cast_mul]
              change ((M : ZMod (M * R)) * (y.val : ZMod (M * R))) * D = 0
              rw [mul_assoc, mul_comm (y.val : ZMod (M * R)) D,
                ← mul_assoc, hmul, zero_mul]
            rw [hy, AddChar.map_zero_eq_one]
      _ = (R : ℂ) := by simp [ZMod.card]
  · rw [if_neg hD]
    apply AddChar.sum_eq_zero_of_ne_one
    rw [AddChar.zmod_char_ne_one_iff R]
    rw [blockLinearCharacter_apply]
    have hnonzero :
        blockKernelAddHom M R (1 : ZMod R) * D ≠ 0 := by
      rw [blockKernelAddHom_apply]
      have hR1 : R ≠ 1 := by
        intro hR
        subst R
        exact hD (Subsingleton.elim _ _)
      rw [ZMod.val_one'' hR1]
      norm_num
      change (M : ZMod (M * R)) * D ≠ 0
      exact (natCast_mul_eq_zero_iff_cast_eq_zero M R D).not.mpr hD
    exact fun hone ↦ hnonzero <|
      ((ZMod.isPrimitive_stdAddChar (M * R)).zmod_char_eq_one_iff
        (M * R) _).mp hone

/-! ## Taylor linearization on a half-size block -/

/-- The block reindexing is addition of its low representative and its
kernel correction. -/
theorem residueBlockEquiv_eq_add_kernel
    (M R : ℕ) [NeZero M] [NeZero R]
    (x : ZMod M) (y : ZMod R) :
    residueBlockEquiv M R (x, y) =
      (x.val : ZMod (M * R)) + blockKernelAddHom M R y := by
  rw [residueBlockEquiv_apply, blockKernelAddHom_apply]
  push_cast
  rfl

/-- If `R ∣ M`, every block correction has square zero modulo `M*R`. -/
theorem blockKernelAddHom_sq_eq_zero
    (M R : ℕ) [NeZero M] [NeZero R] (hRM : R ∣ M)
    (y : ZMod R) :
    (blockKernelAddHom M R y) ^ 2 = 0 := by
  rw [blockKernelAddHom_apply]
  rw [← Nat.cast_pow]
  rw [ZMod.natCast_eq_zero_iff]
  have hbase : M * R ∣ M * M := by
    simpa [Nat.mul_comm] using Nat.mul_dvd_mul_left M hRM
  have hmul : M * R ∣ (M * M) * (y.val * y.val) :=
    dvd_mul_of_dvd_left hbase _
  simpa [pow_two, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hmul

/-- Exact first-order Taylor expansion on a block whose high modulus
divides its low modulus. -/
theorem cubicResidue_residueBlockEquiv
    (M R : ℕ) [NeZero M] [NeZero R] (hRM : R ∣ M)
    (x : ZMod M) (y : ZMod R) :
    CookMagyarFiniteFourier.cubicResidue
        (residueBlockEquiv M R (x, y)) =
      CookMagyarFiniteFourier.cubicResidue (x.val : ZMod (M * R)) +
        blockKernelAddHom M R y *
          CookMagyarLocal.cubicDerivative (x.val : ZMod (M * R)) := by
  rw [residueBlockEquiv_eq_add_kernel]
  simp only [CookMagyarFiniteFourier.cubicResidue,
    CookMagyarLocal.cubicDerivative]
  have hsquare := blockKernelAddHom_sq_eq_zero M R hRM y
  calc
    ((x.val : ZMod (M * R)) + blockKernelAddHom M R y) ^ 3 -
        ((x.val : ZMod (M * R)) + blockKernelAddHom M R y) =
      (x.val : ZMod (M * R)) ^ 3 - x.val +
        blockKernelAddHom M R y *
          (3 * (x.val : ZMod (M * R)) ^ 2 - 1) +
        (blockKernelAddHom M R y) ^ 2 *
          (3 * (x.val : ZMod (M * R)) + blockKernelAddHom M R y) := by ring
    _ = (x.val : ZMod (M * R)) ^ 3 - x.val +
        blockKernelAddHom M R y *
          (3 * (x.val : ZMod (M * R)) ^ 2 - 1) := by rw [hsquare, zero_mul, add_zero]

/-- A prime-power block correction preserves whether a residue is a unit,
provided the low block has positive exponent. -/
theorem isUnit_residueBlockEquiv_primePower_iff
    {p m d : ℕ} [NeZero p] (hp : p.Prime) (hm : 1 ≤ m)
    (x : ZMod (p ^ m)) (y : ZMod (p ^ d)) :
    IsUnit (residueBlockEquiv (p ^ m) (p ^ d) (x, y)) ↔ IsUnit x := by
  rw [residueBlockEquiv_apply]
  rw [← pow_add]
  simpa only [ZMod.natCast_zmod_val] using
    (show
      IsUnit ((x.val + p ^ m * y.val : ℕ) : ZMod (p ^ (m + d))) ↔
        IsUnit ((x.val : ℕ) : ZMod (p ^ m)) by
      rw [ZMod.isUnit_natCast_iff_not_dvd_pow hp (by omega : 0 < m + d),
        ZMod.isUnit_natCast_iff_not_dvd_pow hp (by omega : 0 < m)]
      constructor
      · contrapose!
        intro hx
        exact hx.add (dvd_mul_of_dvd_left (dvd_pow_self p (by omega : m ≠ 0)) y.val)
      · contrapose!
        intro hsum
        exact (Nat.dvd_add_iff_left
          (dvd_mul_of_dvd_left (dvd_pow_self p (by omega : m ≠ 0)) y.val)).mpr hsum)

noncomputable def Internal.PrimePowerStationaryPhaseHelpers.unitsEquivIsUnit (q : ℕ) [NeZero q] :
    (ZMod q)ˣ ≃ {x : ZMod q // IsUnit x} where
  toFun u := ⟨u, u.isUnit⟩
  invFun x := x.property.unit
  left_inv u := by
    apply Units.ext
    exact u.isUnit.unit_spec
  right_inv x := by
    apply Subtype.ext
    exact x.property.unit_spec

private theorem unitCubicExponentialSum_eq_sum_if_isUnit
    {q : ℕ} [NeZero q] (a : ZMod q) :
    unitCubicExponentialSum a =
      ∑ x : ZMod q, if IsUnit x then
        standardAdditiveCharacter
          (a * CookMagyarFiniteFourier.cubicResidue x) else 0 := by
  classical
  let f : ZMod q → ℂ := fun x ↦
    if IsUnit x then standardAdditiveCharacter
      (a * CookMagyarFiniteFourier.cubicResidue x) else 0
  have hsplit := Fintype.sum_subtype_add_sum_subtype
    (fun x : ZMod q ↦ IsUnit x) f
  have hunit : (∑ x : {x : ZMod q // IsUnit x}, f x) =
      unitCubicExponentialSum a := by
    calc
      (∑ x : {x : ZMod q // IsUnit x}, f x) =
          ∑ u : (ZMod q)ˣ, f (Internal.PrimePowerStationaryPhaseHelpers.unitsEquivIsUnit q u) := by
            exact ((Internal.PrimePowerStationaryPhaseHelpers.unitsEquivIsUnit q).sum_comp
              (fun x : {x : ZMod q // IsUnit x} ↦ f x)).symm
      _ = unitCubicExponentialSum a := by
        unfold unitCubicExponentialSum
        apply Finset.sum_congr rfl
        intro u _hu
        simp [f, Internal.PrimePowerStationaryPhaseHelpers.unitsEquivIsUnit]
  have hnonunit : (∑ x : {x : ZMod q // ¬ IsUnit x}, f x) = 0 := by
    apply Finset.sum_eq_zero
    intro x _hx
    simp [f, x.property]
  rw [hunit, hnonunit, add_zero] at hsplit
  simpa [f] using hsplit

/-- Exact stationary-phase decomposition of a unit-restricted complete
cubic sum over a prime-power block.  Orthogonality kills every low residue
whose phase derivative is nonzero modulo the high block. -/
theorem unitCubicExponentialSum_primePower_block
    {p m d : ℕ} [NeZero p] (hp : p.Prime) (hm : 1 ≤ m) (hdm : d ≤ m)
    (a : ZMod (p ^ m * p ^ d)) :
    unitCubicExponentialSum a =
      ∑ x : ZMod (p ^ m), if IsUnit x then
        standardAdditiveCharacter
            (a * CookMagyarFiniteFourier.cubicResidue
              (x.val : ZMod (p ^ m * p ^ d))) *
          (if (((a * cubicDerivative
              (x.val : ZMod (p ^ m * p ^ d))).cast : ZMod (p ^ d)) = 0)
            then (p ^ d : ℂ) else 0)
        else 0 := by
  classical
  let M := p ^ m
  let R := p ^ d
  let e := residueBlockEquiv M R
  let f : ZMod (M * R) → ℂ := fun z ↦
    if IsUnit z then standardAdditiveCharacter
      (a * CookMagyarFiniteFourier.cubicResidue z) else 0
  have hRM : R ∣ M := pow_dvd_pow p hdm
  rw [unitCubicExponentialSum_eq_sum_if_isUnit]
  change (∑ z : ZMod (M * R), f z) = _
  rw [← e.sum_comp f, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro x _hx
  have hunit (y : ZMod R) :
      IsUnit (e (x, y)) ↔ IsUnit x := by
    simpa [M, R, e] using
      isUnit_residueBlockEquiv_primePower_iff hp hm x y
  simp only [f]
  simp_rw [hunit]
  by_cases hxunit : IsUnit x
  · simp only [if_pos hxunit]
    have hphase (y : ZMod R) :
        standardAdditiveCharacter
            (a * CookMagyarFiniteFourier.cubicResidue (e (x, y))) =
          standardAdditiveCharacter
              (a * CookMagyarFiniteFourier.cubicResidue
                (x.val : ZMod (M * R))) *
            blockLinearCharacter M R
              (a * cubicDerivative (x.val : ZMod (M * R))) y := by
      rw [show e (x, y) = residueBlockEquiv M R (x, y) from rfl]
      rw [cubicResidue_residueBlockEquiv M R hRM]
      rw [blockLinearCharacter_apply]
      rw [← AddChar.map_add_eq_mul]
      congr 1
      ring
    simp_rw [hphase]
    rw [← Finset.mul_sum, sum_blockLinearCharacter]
    simp [R]
  · simp only [if_neg hxunit]
    simp

                                                                      
                                     
                                                        
                                                                    
                              
                                                 
                            
                                                                    
                                       
                                                           
                          
             
                            
                                                               
                      

                                                                          
                                                             
                                                         
                                                     
                                                
                                       
                                  
                                                                
                                                                 
                                                        
                                       
             
                                                      
                                                              
                                                 
                           
                                                                    
                                                
                                            
                                 
                                                                      
                        
                                 
                                              
                
                                 
                                                          

                                                                      
                                 
                                                           
                                                         
                  
                                                                           
                                  
                                  
                            
                          
             
                                                       
                                                  
                        

                                                                      
                                                    
                                                         
                  
                                                    
                                                    
                                                                        

                                                          
                                              
                                           
                                            
                                                        
                                                                      
                                               
                  
           
         
                
         

                                                                     
               
                                 
                            
                                                               
                         
         
                       
        
              
                                                                           

                                                                     
                                                                  
                                                                            
                                                 
                                                          
                                                     
                                       
                                                            
                                     
                             
                                        
                                                           
                                                                
                                                                  
                                                         
                                      
                                             
                                            
                                              
            
                                          

                                                                          
                                               
                                                                     
                                                 
                                                
                                                                
                             
                                                                          
       
                               
                                   
                                                     
                                        
                                            
                   
                                      
                                              
                                                      
                                                              
                                   
                                       
                                                                      
                                  
                                                               
                                                          
                             
                                
                                 

                                                                          
                                
                                                          
                            
                            
                                                         
                                  
                                   
                                                          
                                                                   
                    
                                              
      

                                                                     
                        
                                     
                                          
                                         
                                                                    
                        
                                                           
                                                    
                           

                                                      

                                                                      
                                          
theorem isUnit_of_prime_cast_ne_zero
    {p d : ℕ} [NeZero p] (hp : p.Prime) (hd : 0 < d)
    (z : ZMod (p ^ d)) (hz : (z.cast : ZMod p) ≠ 0) : IsUnit z := by
  rw [← ZMod.natCast_zmod_val z]
  rw [ZMod.isUnit_natCast_iff_not_dvd_pow hp hd]
  intro hpz
  apply hz
  rw [ZMod.cast_eq_val, ZMod.natCast_eq_zero_iff]
  exact hpz

/-- For `p ≥ 5`, any two roots of `3X² - 1` modulo a positive power of
`p` differ by a sign. -/
theorem cubicDerivative_root_eq_or_eq_neg
    {p d : ℕ} [NeZero p] (hp : p.Prime) (hp5 : 5 ≤ p) (hd : 0 < d)
    {x y : ZMod (p ^ d)}
    (hx : cubicDerivative x = 0) (hy : cubicDerivative y = 0) :
    y = x ∨ y = -x := by
  letI : Fact p.Prime := ⟨hp⟩
  let castP : ZMod (p ^ d) →+* ZMod p :=
    ZMod.castHom (dvd_pow_self p hd.ne') (ZMod p)
  have hthree : IsUnit (3 : ZMod (p ^ d)) := by
    change IsUnit ((3 : ℕ) : ZMod (p ^ d))
    rw [ZMod.isUnit_natCast_iff_not_dvd_pow hp hd]
    intro hp3
    have hle : p ≤ 3 := Nat.le_of_dvd (by norm_num) hp3
    omega
  have hxunit : IsUnit x := by
    apply IsUnit.of_mul_eq_one (3 * x)
    have hx' : 3 * x ^ 2 = 1 := sub_eq_zero.mp hx
    rw [show x * (3 * x) = 3 * x ^ 2 by ring]
    exact hx'
  have hsq : x ^ 2 = y ^ 2 := by
    apply hthree.mul_left_cancel
    have hx' : 3 * x ^ 2 = 1 := sub_eq_zero.mp hx
    have hy' : 3 * y ^ 2 = 1 := sub_eq_zero.mp hy
    exact hx'.trans hy'.symm
  have hprod : (x - y) * (x + y) = 0 := by
    rw [show (x - y) * (x + y) = x ^ 2 - y ^ 2 by ring, hsq, sub_self]
  have htwo : (2 : ZMod p) ≠ 0 := by
    intro hzero
    have hp2 : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp hzero
    have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) hp2
    omega
  have hxcast : IsUnit (castP x) := hxunit.map castP
  by_cases hdiffcast : castP (x - y) ≠ 0
  · have hdiff : IsUnit (x - y) := by
      apply isUnit_of_prime_cast_ne_zero hp hd
      simpa [castP, ZMod.castHom_apply] using hdiffcast
    right
    have hsumzero : x + y = 0 := by
      apply hdiff.mul_left_cancel
      simpa using hprod
    exact eq_neg_of_add_eq_zero_right hsumzero
  · have hsumcast : castP (x + y) ≠ 0 := by
      intro hsumcast
      have hdiffzero : castP (x - y) = 0 := not_ne_iff.mp hdiffcast
      have h2x : (2 : ZMod p) * castP x = 0 := by
        calc
          (2 : ZMod p) * castP x = castP (x - y) + castP (x + y) := by
            simp only [map_sub, map_add]
            ring
          _ = 0 := by rw [hdiffzero, hsumcast, add_zero]
      exact hxcast.ne_zero ((mul_eq_zero.mp h2x).resolve_left htwo)
    have hsum : IsUnit (x + y) := by
      apply isUnit_of_prime_cast_ne_zero hp hd
      simpa [castP, ZMod.castHom_apply] using hsumcast
    left
    have hdiffzero : x - y = 0 := by
      apply hsum.mul_right_cancel
      simpa using hprod
    exact (sub_eq_zero.mp hdiffzero).symm

/-- Residues where the cubic phase is stationary. -/
def cubicDerivativeRootFinset (p d : ℕ) [NeZero p] :
    Finset (ZMod (p ^ d)) :=
  Finset.univ.filter fun x ↦ cubicDerivative x = 0

/-- At a prime `p ≥ 5`, the cubic derivative has at most two roots modulo
every positive power of `p`. -/
theorem card_cubicDerivativeRootFinset_le_two
    {p d : ℕ} [NeZero p] (hp : p.Prime) (hp5 : 5 ≤ p) (hd : 0 < d) :
    (cubicDerivativeRootFinset p d).card ≤ 2 := by
  classical
  let s := cubicDerivativeRootFinset p d
  change s.card ≤ 2
  by_cases hs : s.Nonempty
  · obtain ⟨x, hx⟩ := hs
    calc
      s.card ≤ ({x, -x} : Finset (ZMod (p ^ d))).card := by
        apply Finset.card_le_card
        intro y hy
        have hxroot : cubicDerivative x = 0 := by
          simpa [s, cubicDerivativeRootFinset] using hx
        have hyroot : cubicDerivative y = 0 := by
          simpa [s, cubicDerivativeRootFinset] using hy
        rcases cubicDerivative_root_eq_or_eq_neg hp hp5 hd hyroot hxroot with
          h | h
        · simp [h]
        · simp [h]
      _ ≤ 2 := Finset.card_le_two
  · rw [Finset.not_nonempty_iff_eq_empty.mp hs]
    simp

/-- Core.Reduction from `p^m` to `p^d` when `d ≤ m`. -/
def primePowerCast (p m d : ℕ) (hdm : d ≤ m) :
    ZMod (p ^ m) →+* ZMod (p ^ d) :=
  ZMod.castHom (pow_dvd_pow p hdm) (ZMod (p ^ d))

                                    
                                                  
                                                           
                      

                                                                        
                         
theorem card_primePowerCast_fiber
    {p m d : ℕ} [NeZero p] (hdm : d ≤ m) (y : ZMod (p ^ d)) :
    Fintype.card {x : ZMod (p ^ m) // primePowerCast p m d hdm x = y} =
      p ^ (m - d) := by
  have hsurj : Function.Surjective (primePowerCast p m d hdm) :=
    ZMod.castHom_surjective (pow_dvd_pow p hdm)
  have hfiber (z : ZMod (p ^ d)) :
      Fintype.card {x : ZMod (p ^ m) // primePowerCast p m d hdm x = z} =
        Fintype.card {x : ZMod (p ^ m) // primePowerCast p m d hdm x = y} := by
    have h := AddMonoidHom.card_fiber_eq_of_mem_range
      (primePowerCast p m d hdm).toAddMonoidHom
      (hsurj z) (hsurj y)
    simpa [Fintype.card_subtype] using h
  have htotal :
      Fintype.card (ZMod (p ^ m)) =
        Fintype.card (Σ z : ZMod (p ^ d),
          {x : ZMod (p ^ m) // primePowerCast p m d hdm x = z}) :=
    Fintype.card_congr
      (Equiv.sigmaFiberEquiv (primePowerCast p m d hdm)).symm
  have hcard : p ^ m = p ^ d *
      Fintype.card {x : ZMod (p ^ m) // primePowerCast p m d hdm x = y} := by
    calc
      p ^ m = Fintype.card (ZMod (p ^ m)) := (ZMod.card _).symm
      _ = Fintype.card (Σ z : ZMod (p ^ d),
          {x : ZMod (p ^ m) // primePowerCast p m d hdm x = z}) := htotal
      _ = ∑ z : ZMod (p ^ d),
          Fintype.card {x : ZMod (p ^ m) // primePowerCast p m d hdm x = z} :=
        Fintype.card_sigma
      _ = ∑ _z : ZMod (p ^ d),
          Fintype.card {x : ZMod (p ^ m) // primePowerCast p m d hdm x = y} := by
        apply Finset.sum_congr rfl
        intro z _hz
        exact hfiber z
      _ = p ^ d * Fintype.card
          {x : ZMod (p ^ m) // primePowerCast p m d hdm x = y} := by
        simp [ZMod.card]
  have hpow : p ^ m = p ^ d * p ^ (m - d) := by
    rw [← pow_add]
    congr 1
    omega
  apply Nat.eq_of_mul_eq_mul_left (pow_pos (NeZero.pos p) d)
  exact hcard.symm.trans hpow

@[simp] theorem primePowerCast_cubicDerivative
    (p m d : ℕ) (hdm : d ≤ m) (x : ZMod (p ^ m)) :
    primePowerCast p m d hdm (cubicDerivative x) =
      cubicDerivative (primePowerCast p m d hdm x) := by
  unfold cubicDerivative
  simp only [map_sub, map_mul, map_pow, map_ofNat, map_one]

/-- Low residues whose cubic derivative vanishes after reduction to
`p^d`. -/
def cubicDerivativeCastRootFinset
    (p m d : ℕ) [NeZero p] (hdm : d ≤ m) :
    Finset (ZMod (p ^ m)) :=
  Finset.univ.filter fun x ↦
    primePowerCast p m d hdm (cubicDerivative x) = 0

/-- The number of stationary low residues is the number of roots modulo
`p^d` times the common reduction-fiber cardinality. -/
theorem card_cubicDerivativeCastRootFinset_eq
    (p m d : ℕ) [NeZero p] (hdm : d ≤ m) :
    (cubicDerivativeCastRootFinset p m d hdm).card =
      (cubicDerivativeRootFinset p d).card * p ^ (m - d) := by
  classical
  let castP := primePowerCast p m d hdm
  let P : ZMod (p ^ m) → Prop := fun x ↦
    castP (cubicDerivative x) = 0
  let f : ZMod (p ^ m) → ℕ := fun x ↦ if P x then 1 else 0
  have he := (Equiv.sigmaFiberEquiv castP).sum_comp f
  have hleft : (cubicDerivativeCastRootFinset p m d hdm).card =
      ∑ x : ZMod (p ^ m), f x := by
    unfold cubicDerivativeCastRootFinset
    simp [P, f, castP]
  have hright : (cubicDerivativeRootFinset p d).card =
      ∑ y : ZMod (p ^ d), if cubicDerivative y = 0 then 1 else 0 := by
    unfold cubicDerivativeRootFinset
    simp
  rw [hleft, hright]
  rw [← he, Fintype.sum_sigma, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro y _hy
  by_cases hyroot : cubicDerivative y = 0
  · simp only [hyroot, if_true, one_mul]
    calc
      (∑ x : {x : ZMod (p ^ m) // castP x = y}, f x) =
          ∑ _x : {x : ZMod (p ^ m) // castP x = y}, 1 := by
        apply Finset.sum_congr rfl
        intro x _hx
        have hxP : P x := by
          unfold P castP
          rw [primePowerCast_cubicDerivative, x.property, hyroot]
        simp [f, hxP]
      _ = Fintype.card {x : ZMod (p ^ m) // castP x = y} := by simp
      _ = p ^ (m - d) := by
        simpa [castP] using card_primePowerCast_fiber hdm y
  · simp only [hyroot, if_false, zero_mul]
    apply Finset.sum_eq_zero
    intro x _hx
    have hxnotP : ¬ P x := by
      intro hxP
      apply hyroot
      unfold P castP at hxP
      rw [primePowerCast_cubicDerivative, x.property] at hxP
      exact hxP
    simp [f, hxnotP]

/-- For `p ≥ 5`, at most `2p^(m-d)` low residues are stationary modulo
`p^d`. -/
theorem card_cubicDerivativeCastRootFinset_le
    {p m d : ℕ} [NeZero p] (hp : p.Prime) (hp5 : 5 ≤ p)
    (hd : 0 < d) (hdm : d ≤ m) :
    (cubicDerivativeCastRootFinset p m d hdm).card ≤
      2 * p ^ (m - d) := by
  rw [card_cubicDerivativeCastRootFinset_eq]
  exact Nat.mul_le_mul_right (p ^ (m - d))
    (card_cubicDerivativeRootFinset_le_two hp hp5 hd)

private theorem cast_cubicDerivative_natCast_eq_primePowerCast
    (p m d : ℕ) [NeZero p] (hdm : d ≤ m) (x : ZMod (p ^ m)) :
    ZMod.castHom (dvd_mul_left (p ^ d) (p ^ m)) (ZMod (p ^ d))
        (cubicDerivative (x.val : ZMod (p ^ m * p ^ d))) =
        primePowerCast p m d hdm (cubicDerivative x) := by
  unfold cubicDerivative primePowerCast
  simp only [map_sub, map_mul, map_pow, map_ofNat, map_one]
  congr 1
  simp only [ZMod.castHom_apply]
  rw [ZMod.cast_natCast (dvd_mul_left (p ^ d) (p ^ m)) x.val,
    ZMod.cast_eq_val]

                                                                      
                                                        
                                                  
                                                             
                                                         
                                                   
                          
                                          
                                           
                                                         
                               
                              
                                  
            
                           
                                 
                                                               
                        
             
                                                  
                              
                                  
            
                           
                                 
                                                               
                     
            
                              
                                  
            
                           
                                 
                                                               
                        
             
                                                  
                              
                                  
            
                           
                                 
                                                               
                     
            
                                                            
                             
                                                        
                                                 
                          
                                                             
            
              

                                                                          
                                                                          
                                                                        
                    
                                                       
                        
                                                
                                       
                                  
                                                        
                                                  
            
                                                         
                                                              
                                                      
                                                               
                      
                                                                    
                                                                   
                                                                      
             
                                      
                                                
                            
                                                                         
                                    
                             
                                                             
                                 
                                                       

                                                                      
                                                                        
                
                                                         
                                           
                                                     
                                                   
                        
                                             
                         
                               
                                                                        
                                                         
                                                     
                            
               
                                                                      
                 
                                      
                       
                                                                          
                                                           
                                                 
           
      

                                                                            
                                                            
                                           
                                                     
                                                 
                           
                                                                      

                                                                        
                            
                                                     
                                           
                                                                          
                                                                    
                                                               
                                                                  

                                                                          
                                                     
                                                 
                            
                                                    
                                                            
                                                          
                                                                
                                                 
                                                        
                                           
                         
                                                    
                                                
              
                                                                     

                                                            
                                                      
                                                               
                              
                                                                 
                                           
             
                                                                   
                                            
                                          
           
                                    
                                
          
                                      
                               
                                                             
                                                   
                                                               
                               

                                                     
                                  
                                                    
                                        
                             
                            
                                
          
                         
                               
                                                             
                    
           
                                                
                            
                                
          
                         
                               
                                                             
              
                                                   
                            
                                
          
                         
                               
                                                             
                    
           
                                                
                            
                                
          
                         
                               
                                                             
              
          

                                                   
                                                       
                                                               
      
                                                       
                                      
                                                            
                                
                 
                                                                      
          
                                                                 

                                                      
                                  
                                                    
                                        
                             
                            
                                
          
                         
                               
                                                             
                    
           
                                                
                            
                                
          
                         
                               
                                                             
              
          
                            
                                
          
                         
                               
                                                             
                    
           
                                                
                            
                                
          
                         
                               
                                                             
              
          
                            
                                
          
                         
                               
                                                             
                    
           
                                                
                            
                                
          
                         
                               
                                                             
              
          
                            
                                
          
                         
                               
                                                             
                    
           
                                                
                            
                                
          
                         
                               
                                                             
              
          

                                                   
                                                        
                                                               
      
                                                       
                                      
                                                            
                                
                 
                                                                       
          
                                                                 

                                                                  
                                 
                                                       
               
                                                                           
                                                       
                                              
                                  
                                                     
                                         
             
                                                                   
                                          
                                      
           
                              
        
                                  
                             
                                                           
                                           
                                                     
                                                        
                                                                
           
             
                       
                     
                                                           
                                               
                                                         
                                                
        
                           
                                                           
                                                  
                                    
                   
                        
                 
                                         
           
      

                                                                     
                                                                          
                                                                 
                                                            
               
                                                                           
                      
                                                         
                                                
                                  
                                                        
                                                                 
                                           
                                                     
           
                       
                                                        
                  
            
      
                                    
                        
                                                           
                                               
                                       
                        
                                                           
                                                       
                                     

                                                                      
                                                                   
                 
                                                             
               
                                                                           
                      
                                                         
                                                
                                  
                                                        
                                                                  
                                           
                                                     
           
                       
                                                        
                  
            
      
                                    
                        
                                                           
                                               
                                       
                        
                                                           
                                                       
                                     

                                                                  
                                                                      
                                                           
                                                            
                            
                                                    
                                                           
                                              
                         
                                                           
                                               
                         
                                                           
                                                   
                                                   
                                                                          
                                                                          
                                                                          
                                                      
                                                         
                                                          

                                                                           
                                                             
                                                  
                                         
                                                            
                       
                                            
                                                                 
                                            
                                                                 
                                            
                                                         
                                                              
                                               
                                                                       
          

                                                                         
                                                 
                                                     
                                          
                                                                 
                                                        
                                                       
          

                                                                 
                                                               
theorem norm_unitCubicExponentialSum_primePower_block_le
    {p m d : ℕ} [NeZero p] (hp : p.Prime) (hp5 : 5 ≤ p)
    (hm : 1 ≤ m) (hd : 0 < d) (hdm : d ≤ m)
    (a : ZMod (p ^ m * p ^ d)) (ha : IsUnit a) :
    ‖unitCubicExponentialSum a‖ ≤ 2 * (p : ℝ) ^ m := by
  classical
  let s := cubicDerivativeCastRootFinset p m d hdm
  let castHigh : ZMod (p ^ m * p ^ d) →+* ZMod (p ^ d) :=
    ZMod.castHom (dvd_mul_left (p ^ d) (p ^ m)) (ZMod (p ^ d))
  have haHigh : IsUnit (castHigh a) := ha.map castHigh
  have hcondition (x : ZMod (p ^ m)) :
      (((a * cubicDerivative
        (x.val : ZMod (p ^ m * p ^ d))).cast : ZMod (p ^ d)) = 0) ↔
          x ∈ s := by
    have hderiv := cast_cubicDerivative_natCast_eq_primePowerCast
      p m d hdm x
    change castHigh (cubicDerivative
      (x.val : ZMod (p ^ m * p ^ d))) =
        primePowerCast p m d hdm (cubicDerivative x) at hderiv
    change castHigh (a * cubicDerivative
      (x.val : ZMod (p ^ m * p ^ d))) = 0 ↔ x ∈ s
    rw [map_mul, hderiv]
    constructor
    · intro hzero
      have hderivzero : primePowerCast p m d hdm (cubicDerivative x) = 0 := by
        apply haHigh.mul_left_cancel
        simpa using hzero
      simpa [s, cubicDerivativeCastRootFinset] using hderivzero
    · intro hx
      have hderivzero : primePowerCast p m d hdm (cubicDerivative x) = 0 := by
        simpa [s, cubicDerivativeCastRootFinset] using hx
      rw [hderivzero, mul_zero]
  rw [unitCubicExponentialSum_primePower_block hp hm hdm a]
  calc
    ‖∑ x : ZMod (p ^ m), if IsUnit x then
        standardAdditiveCharacter
            (a * CookMagyarFiniteFourier.cubicResidue
              (x.val : ZMod (p ^ m * p ^ d))) *
          (if (((a * cubicDerivative
              (x.val : ZMod (p ^ m * p ^ d))).cast : ZMod (p ^ d)) = 0)
            then (p ^ d : ℂ) else 0)
        else 0‖ ≤
      ∑ x : ZMod (p ^ m), ‖if IsUnit x then
        standardAdditiveCharacter
            (a * CookMagyarFiniteFourier.cubicResidue
              (x.val : ZMod (p ^ m * p ^ d))) *
          (if (((a * cubicDerivative
              (x.val : ZMod (p ^ m * p ^ d))).cast : ZMod (p ^ d)) = 0)
            then (p ^ d : ℂ) else 0)
        else 0‖ := norm_sum_le _ _
    _ ≤ ∑ x : ZMod (p ^ m),
        if x ∈ s then (p ^ d : ℝ) else 0 := by
      apply Finset.sum_le_sum
      intro x _hx
      by_cases hxs : x ∈ s
      · have hc := (hcondition x).2 hxs
        by_cases hxunit : IsUnit x
        · rw [if_pos hxunit, if_pos hc]
          simp [hxs, AddChar.norm_apply]
        · rw [if_neg hxunit]
          simp [hxs]
      · have hc := (hcondition x).not.mpr hxs
        by_cases hxunit : IsUnit x
        · rw [if_pos hxunit, if_neg hc]
          simp [hxs]
        · rw [if_neg hxunit]
          simp [hxs]
    _ = ∑ _x ∈ s, (p ^ d : ℝ) :=
      Finset.sum_ite_mem_eq s (fun _x ↦ (p ^ d : ℝ))
    _ = (s.card : ℝ) * (p ^ d : ℝ) := by
      simp [nsmul_eq_mul]
    _ ≤ ((2 * p ^ (m - d) : ℕ) : ℝ) * (p ^ d : ℝ) := by
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast card_cubicDerivativeCastRootFinset_le hp hp5 hd hdm
      · positivity
    _ = 2 * (p : ℝ) ^ m := by
      push_cast
      have hpowers : (p : ℝ) ^ (m - d) * (p : ℝ) ^ d =
          (p : ℝ) ^ m := by
        rw [← pow_add, Nat.sub_add_cancel hdm]
      rw [mul_assoc, hpowers]

/-- The stationary-phase estimate summed over all unit frequencies and
normalized as a singular-series coefficient. -/
theorem norm_singularSeriesTerm_primePower_block_le
    {p m d n T : ℕ} [NeZero p] (hp : p.Prime) (hp5 : 5 ≤ p)
    (hm : 1 ≤ m) (hd : 0 < d) (hdm : d ≤ m) :
    ‖singularSeriesTerm n T (p ^ m * p ^ d)‖ ≤
      ‖((Nat.totient (p ^ m * p ^ d) : ℂ)⁻¹)‖ ^ n *
        (Nat.totient (p ^ m * p ^ d) : ℝ) *
          (2 * (p : ℝ) ^ m) ^ n := by
  rw [singularSeriesTerm_of_pos n T (by positivity)]
  unfold singularSeriesCoefficient
  rw [norm_mul, norm_pow]
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  calc
    ‖∑ a : (ZMod (p ^ m * p ^ d))ˣ,
        unitCubicExponentialSum (a : ZMod (p ^ m * p ^ d)) ^ n *
          standardAdditiveCharacter
            (-((a : ZMod (p ^ m * p ^ d)) *
              (T : ZMod (p ^ m * p ^ d))))‖ ≤
        ∑ a : (ZMod (p ^ m * p ^ d))ˣ,
          ‖unitCubicExponentialSum (a : ZMod (p ^ m * p ^ d)) ^ n *
            standardAdditiveCharacter
              (-((a : ZMod (p ^ m * p ^ d)) *
                (T : ZMod (p ^ m * p ^ d))))‖ := norm_sum_le _ _
    _ ≤ ∑ _a : (ZMod (p ^ m * p ^ d))ˣ,
        (2 * (p : ℝ) ^ m) ^ n := by
      apply Finset.sum_le_sum
      intro a _ha
      have hsum := norm_unitCubicExponentialSum_primePower_block_le
        hp hp5 hm hd hdm (a : ZMod (p ^ m * p ^ d)) a.isUnit
      calc
        ‖unitCubicExponentialSum (a : ZMod (p ^ m * p ^ d)) ^ n *
            standardAdditiveCharacter
              (-((a : ZMod (p ^ m * p ^ d)) *
                (T : ZMod (p ^ m * p ^ d))))‖ =
            ‖unitCubicExponentialSum
              (a : ZMod (p ^ m * p ^ d))‖ ^ n := by
                simp [norm_pow, AddChar.norm_apply]
        _ ≤ (2 * (p : ℝ) ^ m) ^ n :=
          pow_le_pow_left₀
            (norm_nonneg (unitCubicExponentialSum
              (a : ZMod (p ^ m * p ^ d)))) hsum n
    _ = (Nat.totient (p ^ m * p ^ d) : ℝ) *
        (2 * (p : ℝ) ^ m) ^ n := by
      simp [ZMod.card_units_eq_totient, nsmul_eq_mul]

                                                                
                     
                                                  
                                                         
                  
                                            
                                                 
                                         
                                     
                                                       
                                                
                                   
                                         

                                                                        
                                    
                                                 
                                                         
                  
                                                
                                                     
                                             
                                           
                                                       
                                                    
                                           
                                               
                                      

end CookMagyarPrimePower
end SystolicGrowth
