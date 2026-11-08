module
public import Examples.pmaronow__fluctuations_palomar.Dependencies.v0a4b81a5fb16.SKConstants.RectangleBound
public import Mathlib
public import Mathlib.Data.Fin.Embedding
public import Mathlib.Data.Fintype.Sum
import Mathlib.Tactic
public section
noncomputable section
namespace SKConstants
end SKConstants
namespace SKConstants.DyadicCore
@[expose, reducible] def leafCount : ℕ → ℕ
  | 0 => 1
  | r + 1 => leafCount r + leafCount r
@[expose, reducible] def Node : ℕ → Type
  | 0 => Empty
  | r + 1 => Unit ⊕ (Node r ⊕ Node r)
instance nodeFintype : (r : ℕ) → Fintype (Node r)
  | 0 => inferInstanceAs (Fintype Empty)
  | r + 1 => by
    letI := nodeFintype r
    exact inferInstanceAs (Fintype (Unit ⊕ (Node r ⊕ Node r)))
instance nodeDecidableEq : (r : ℕ) → DecidableEq (Node r)
  | 0 => inferInstanceAs (DecidableEq Empty)
  | r + 1 => by
    letI := nodeDecidableEq r
    exact inferInstanceAs (DecidableEq (Unit ⊕ (Node r ⊕ Node r)))
@[expose] def left : (r : ℕ) → Node r → Finset (Fin (leafCount r))
  | 0, node => nomatch node
  | r + 1, .inl _ => Finset.univ.map (Fin.castAddEmb (leafCount r))
  | r + 1, .inr (.inl node) => (left r node).map (Fin.castAddEmb (leafCount r))
  | r + 1, .inr (.inr node) => (left r node).map (Fin.natAddEmb (leafCount r))
@[expose] def right : (r : ℕ) → Node r → Finset (Fin (leafCount r))
  | 0, node => nomatch node
  | r + 1, .inl _ => Finset.univ.map (Fin.natAddEmb (leafCount r))
  | r + 1, .inr (.inl node) => (right r node).map (Fin.castAddEmb (leafCount r))
  | r + 1, .inr (.inr node) => (right r node).map (Fin.natAddEmb (leafCount r))
end SKConstants.DyadicCore
namespace SKConstants
end SKConstants
