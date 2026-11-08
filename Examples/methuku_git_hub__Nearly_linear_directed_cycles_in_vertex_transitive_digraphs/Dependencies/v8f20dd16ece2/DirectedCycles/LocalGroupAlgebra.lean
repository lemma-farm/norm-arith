module
public import Mathlib.Tactic
set_option autoImplicit false
@[expose] public section
set_option autoImplicit false
namespace DirectedCycles
/-- Algebraic part of a symmetric local group. Multiplication is a functional
relation so that undefined products cannot accidentally be used as elements.
Associativity applies only when both bracketings are defined. -/
structure LocalGroupAlgebra (G : Type*) where
  one : G
  inv : G → G
  mulRel : G → G → G → Prop
  unique : ∀ {a b c d}, mulRel a b c → mulRel a b d → c = d
  one_mul : ∀ a, mulRel one a a
  mul_one : ∀ a, mulRel a one a
  inv_mul : ∀ a, mulRel (inv a) a one
  mul_inv : ∀ a, mulRel a (inv a) one
  assoc : ∀ {a b c ab bc x y}, mulRel a b ab → mulRel b c bc →
    mulRel ab c x → mulRel a bc y → x = y
namespace LocalGroupAlgebra
variable {G : Type*} (L : LocalGroupAlgebra G)
def restrict (S : Set G) (h1 : L.one ∈ S) (hi : ∀ x ∈ S, L.inv x ∈ S) : LocalGroupAlgebra S where
  one := ⟨L.one,h1⟩
  inv x := ⟨L.inv x.val,hi x.val x.property⟩
  mulRel x y z := L.mulRel x.val y.val z.val
  unique h h' := Subtype.ext (L.unique h h')
  one_mul x := L.one_mul x.val
  mul_one x := L.mul_one x.val
  inv_mul x := L.inv_mul x.val
  mul_inv x := L.mul_inv x.val
  assoc h₁ h₂ h₃ h₄ := Subtype.ext (L.assoc h₁ h₂ h₃ h₄)
structure Cancellative : Prop where
  left_cancel : ∀ {a b c d}, L.mulRel a b d → L.mulRel a c d → b = c
  right_cancel : ∀ {a b c d}, L.mulRel b a d → L.mulRel c a d → b = c
  inv_product : ∀ {a b c d}, L.mulRel a b c → L.mulRel (L.inv b) (L.inv a) d → L.inv c = d
theorem Cancellative.restrict (hL : L.Cancellative) (S : Set G) (h1 : L.one ∈ S)
    (hi : ∀ x ∈ S, L.inv x ∈ S) : (L.restrict S h1 hi).Cancellative where
  left_cancel h h' := Subtype.ext (hL.left_cancel h h')
  right_cancel h h' := Subtype.ext (hL.right_cancel h h')
  inv_product h h' := Subtype.ext (hL.inv_product h h')
end LocalGroupAlgebra
end DirectedCycles
