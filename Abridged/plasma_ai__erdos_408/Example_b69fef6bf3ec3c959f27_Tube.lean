module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Set.Card
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.NumberTheory.DirichletCharacter.Basic
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Basic.Complex.Basic

-- ==== Examples.plasma_ai__erdos_408.Dependencies.v2536eee0f99d.Erdos408.Hypotheses ====
public section
set_option autoImplicit false
/-!
# The graph-paper results

The results of *The Poisson–Dirichlet law for prime predecessors* (PD)
and *Weighted dilation graphs, smooth shifted primes and totient fibers* (WD)
from which the rectangle statistic is derived. Put `L = log x`, `T = log L`,
`s = log T` and `W = exp(L^{0.24})`; an integer is *rough* if it has no
prime factor at most `W`.

* `OneSidedTypeII` is PD Theorem 3.1 for every coefficient `α` with the
  properties its proof uses: support in `[H_m, 2H_m]`, roughness, a
  logarithmic size bound, and the twisted cancellation of PD Lemma 5.2. The
  scales may shrink to `x^γ` with `γ ≥ L^{-1/100}`, and the band exponents
  may vary in a fixed window with a fixed gap. The integer-kernel bound that
  PD's Lemma 5.3 derives at fixed scales is a premise. It is proved as
  `oneSidedTypeII` in `Erdos408.OneSided`, so it is no longer a hypothesis.
* `TwoSidedCorrelation` is PD Theorem 6.1 with a bounded joint coefficient
  on all slots but the last, slot margins `x^{cT^{-20}}`, a clipped
  invariant core, up to `O(s)` varying inert bands, and cutoffs with
  `T^{O(1)}` derivatives. The two analytic estimates its proof needs at
  those margins, replacing PD (6.37) and (6.38), are premises. It is proved
  as `twoSidedCorrelation_of_graphTransference` in `Erdos408.TwoSided`,
  following PD §6.
* `GraphTransference` is PD Propositions 6.2 and 6.3 composed: WD's local
  transference and residual ideal family, for endpoints that depend on the
  position alone. It is proved as `graphTransference` in `Erdos408.Graph`,
  from the vendored formalization of WD (`vendor/TotientFibers/`).
* `BlockSieve` is WD Lemma 2.9 (PD Lemma 2.6) as printed, with the implicit
  `z ≥ 1`. It is proved as `blockSieve` in `Erdos408.BlockSieve`, so it is no
  longer a hypothesis.

`OneSidedTypeII` and `TwoSidedCorrelation` are *not* the printed theorems.
The printed statements fix the scale, the margin, the bands and the proxy,
and give no rate, so they do not imply the rectangle statistic. These are
the extensions that the extraction of *The normal order of the number of
iterations of Euler's function* (Plasma AI, 2026), §6, uses and argues the
printed proofs support; both are proved here.

No statement here uses a zero-free region: every analytic estimate is a
premise, proved separately from the vendored zero-free half-plane. See
`blueprint/rectangle_input.md` for the statements and their justification.

None of these definitions appears in `Challenge.lean`, whose theorems have no
hypotheses.
-/
@[expose] public section
open Filter
namespace Erdos408

/-- The band of primes `exp(L^a) ≤ p ≤ exp(2 L^a)`. -/
noncomputable def band (x a : ℝ) : Finset ℕ :=
  (Finset.Icc ⌈Real.exp (Real.log x ^ a)⌉₊ ⌊Real.exp (2 * Real.log x ^ a)⌋₊).filter Nat.Prime

/-- The harmonic mass `∑_{p ∈ S} 1 / p`. -/
noncomputable def harmonicMass (S : Finset ℕ) : ℝ :=
  ∑ p ∈ S, (1 : ℝ) / p

end Erdos408

end
end

-- ==== Examples.plasma_ai__erdos_408.Dependencies.v2536eee0f99d.Erdos408.OneSided.Setup ====
public section
set_option autoImplicit false
/-!
# Setup for the one-sided Type II estimate

The objects of `blueprint/one_sided_type_ii.md` §§0–1 and §3: the varying data of
`OneSidedTypeII` at one `x`, its hypotheses, the parameter choices, and the two squares
compared in the proof.

* `Data` bundles the band exponents, the scale exponent, the scales `H_m, H_n`, the
  invariant endpoint `F` and the coefficients `α, β`. `Admissible` is the list of
  hypotheses of `OneSidedTypeII` on them apart from the twisted cancellation P4
  (`TwistBound`) and the kernel premise (G) (`KernelBound`).
* The exponents `D₁, E₀, G, A₀, K₀, B, A` of blueprint §1 depend only on `(D_*, C)`.
* `cauchySquare` is the Cauchy square `Q_Y` of PD (3.8): pairs of label products
  `a, b ≍ Y` with `mn - 1 = ah`, `rs - 1 = bh` for a common `h`.
* `majorSquare` is the major sum `Q_Y^maj` of PD (5.1), in which the equation
  `bmn - ars = b - a` is replaced by the major-arc kernel `𝓗_𝔐`.
-/
@[expose] public section
noncomputable section
namespace Erdos408.OneSided
open Finset Real
/-- The varying data of `OneSidedTypeII` at one `x`: the band exponents, the scale exponent
`γ`, the scales `H_m, H_n`, the invariant endpoint `F` and the coefficients `α, β`. -/
structure Data (K : ℕ) where
  a : Fin K → ℝ
  γ : ℝ
  Hm : ℝ
  Hn : ℝ
  F : ℕ → ℂ
  α : ℕ → ℂ
  β : ℕ → ℂ
namespace Data
variable {K : ℕ} (d : Data K)

/-- The range `[H_m, 2H_m]` of the marked variable. -/
def mRange : Finset ℕ := Icc ⌈d.Hm⌉₊ ⌊2 * d.Hm⌋₊

/-- `∏_i V_i`, the product of the harmonic masses of the bands. -/
def bandMass (x : ℝ) : ℝ := ∏ i, harmonicMass (band x (d.a i))
end Data
variable {K : ℕ}

/-! ### Parameters (blueprint §1) -/

/-! ### Cutoffs and arcs -/
/-- The dyadic bump `η(y) = s(y) - s(y/2)` with `s(y) = smoothTransition (y - 1)`. It is
smooth, supported in `[1, 4]`, and `∑_j η(b / 2^j) = 1` for `b ≥ 2`. -/
def dyadicBump (y : ℝ) : ℝ := smoothTransition (y - 1) - smoothTransition (y / 2 - 1)
/-- The plateau `ψ(t) = smoothTransition (5 - |t|)`: smooth, equal to one on `[-4, 4]` and
supported in `[-5, 5]`. -/
def plateau (t : ℝ) : ℝ := smoothTransition (5 - |t|)
/-- `∫_𝔐 e(θ n) dθ`, summed arc by arc over `|θ - h/k| ≤ 2 L^{A₀} / Y` with
`1 ≤ k ≤ L^{A₀}` and `(h, k) = 1`. -/
def arcIntegral (A₀ x Y : ℝ) (n : ℤ) : ℂ :=
  ∑ k ∈ Icc 1 ⌊Real.log x ^ A₀⌋₊, ∑ h ∈ (range k).filter (fun h => Nat.Coprime h k),
    ∫ θ in (-(2 * Real.log x ^ A₀ / Y))..(2 * Real.log x ^ A₀ / Y),
      Complex.exp (2 * π * Complex.I * ((((h : ℝ) / k + θ) * n : ℝ) : ℂ))

/-! ### The two squares -/

end Erdos408.OneSided

end
end
end

-- ==== Examples.plasma_ai__erdos_408.Dependencies.v2536eee0f99d.Erdos408.OneSided.Lift ====
public section
set_option autoImplicit false
/-!
# The lift

The physical states and operators of PD §3.2 (`blueprint/one_sided_type_ii.md` §4), at a
fixed label dyad `Y` and pad dyad `d₀`.

* A state is a primitive position `P ∈ Ω = [U, 16U] × [V, 2V]`, with `U = d₀ Y H_m` and
  `V = H_n`, together with ordered lists of `M = J + 1` distinct primes of each band, all
  dividing `P₁`. The state measure `∏_i V_i^{-M}` is constant, so adjoints are conjugate
  transposes.
* `rowOp` is the row operation `𝒯`: it copies the pads (slots `0, …, J - 1`), replaces
  the last slot of each group by a new label distinct from every source label (the
  cross-edge ban), and has the multiplier `𝒦` of PD `eq:det-kernel`. `symOp` averages over the
  orders of the lists, `goodOp` projects onto good states, and
  `edgeOp = 𝒢 𝒮 𝒯 𝒮 𝒢` is the operator `𝒜`.
* `endVec` is the endpoint vector `f = ᾱ_m β_{P₂}` with `m = P₁ / (list product)`; the
  vector `g` of PD `det:endpoints` equals `f`. `rowPairing` and `pairing` are `⟨f, 𝒯 f⟩` and
  `⟨f, 𝒜 f⟩`, and `detMoment` is `∑_P ⟨u_P, (𝒜𝒜^*)^R u_P⟩`.

The damping exponent `q` of the lift is a free parameter: it equals one at the endpoints,
so it affects only the moment.
-/
@[expose] public section
noncomputable section
namespace Erdos408.OneSided
open Finset Real
open scoped Matrix
variable {K : ℕ}
/-- `J = ⌊L^{0.01}⌋`, the number of pads in each group. -/
def padCount (x : ℝ) : ℕ := ⌊Real.log x ^ (1 / 100 : ℝ)⌋₊
/-- `R = ⌈L^{1/2} / 2⌉`; the moment has `N = 2R` edges. -/
def momentPower (x : ℝ) : ℕ := ⌈Real.log x ^ (1 / 2 : ℝ) / 2⌉₊
/-- Ordered lists of `J + 1` labels in each of the `K` groups. -/
abbrev Lists (K J : ℕ) := Fin K → Fin (J + 1) → ℕ

open scoped Classical in
/-- The ordered lists of `J + 1` distinct primes of each band. -/
def lists (x : ℝ) (d : Data K) (J : ℕ) : Finset (Lists K J) :=
  (Fintype.piFinset fun i => Fintype.piFinset fun _ : Fin (J + 1) => band x (d.a i)).filter
    fun p => ∀ i, Function.Injective (p i)

/-! ### Products of labels -/
/-- The product of all labels. -/
def listProd {J : ℕ} (p : Lists K J) : ℕ := ∏ i, ∏ h, p i h
/-- The pad product `D`: the labels in slots `0, …, J - 1`. -/
def padProd {J : ℕ} (p : Lists K J) : ℕ := ∏ i, ∏ h : Fin J, p i h.castSucc
/-- The product of the last slots. -/
def lastProd {J : ℕ} (p : Lists K J) : ℕ := ∏ i, p i (Fin.last J)
/-- The product of the labels after omitting slot `o i` in each group `i`. -/
def omitProd {J : ℕ} (p : Lists K J) (o : Fin K → Fin (J + 1)) : ℕ :=
  ∏ i, ∏ h ∈ univ.erase (o i), p i h
/-! ### Good states -/

/-- The distance `‖t‖` from `t` to the nearest integer. -/
def circleDist (t : ℝ) : ℝ := |t - round t|
/-- Test (i) of PD §3.2 at the ratio `r`: for every omission product `D ∈ [d₀, 2d₀)` and
`1 ≤ l ≤ Y^{0.2}`, `‖l D r‖ > Y^{-0.7}`. -/
def GoodFirst (Y d₀ : ℝ) {J : ℕ} (r : ℝ) (p : Lists K J) : Prop :=
  ∀ o : Fin K → Fin (J + 1), d₀ ≤ (omitProd p o : ℝ) → (omitProd p o : ℝ) < 2 * d₀ →
    ∀ l : ℕ, 1 ≤ l → (l : ℝ) ≤ Y ^ (1 / 5 : ℝ) →
      Y ^ (-(7 / 10 : ℝ)) < circleDist (l * omitProd p o * r)
/-- The fresh draws outside `I`: a prime of `𝒫_i` for `i ∉ I`, and `1` for `i ∈ I`. -/
def freshDraws (x : ℝ) (d : Data K) (I : Finset (Fin K)) : Finset (Fin K → ℕ) :=
  Fintype.piFinset fun i => if i ∈ I then {1} else band x (d.a i)
/-- The probability `∏_{i ∉ I} μ_i(T_i)` of a fresh draw, `μ_i(p) = 1 / (p V_i)`. -/
def freshWeight (x : ℝ) (d : Data K) (I : Finset (Fin K)) (T : Fin K → ℕ) : ℝ :=
  ∏ i ∈ univ.filter (· ∉ I), 1 / ((T i : ℝ) * harmonicMass (band x (d.a i)))
/-- The selections `Z`: a prime of `𝒫_j` for `j ∈ I \ {i}`, and `1` otherwise. -/
def selections (x : ℝ) (d : Data K) (I : Finset (Fin K)) (i : Fin K) : Finset (Fin K → ℕ) :=
  Fintype.piFinset fun j => if j ∈ I.erase i then band x (d.a j) else {1}
/-- For the fresh draw `T`, the points `D Z T r` belonging to distinct integers `D Z` are
pairwise at circle distance at least `100 e^{-L^{a_i}}`. Here `D` ranges over the omission
products in `[d₀, 2d₀)`. -/
def Separated (x : ℝ) (d : Data K) (d₀ : ℝ) (I : Finset (Fin K)) (i : Fin K) {J : ℕ}
    (r : ℝ) (p : Lists K J) (T : Fin K → ℕ) : Prop :=
  ∀ o o' : Fin K → Fin (J + 1), ∀ Z ∈ selections x d I i, ∀ Z' ∈ selections x d I i,
    d₀ ≤ (omitProd p o : ℝ) → (omitProd p o : ℝ) < 2 * d₀ →
    d₀ ≤ (omitProd p o' : ℝ) → (omitProd p o' : ℝ) < 2 * d₀ →
    omitProd p o * ∏ j, Z j ≠ omitProd p o' * ∏ j, Z' j →
    100 * Real.exp (-Real.log x ^ d.a i) ≤
      circleDist (((omitProd p o * ∏ j, Z j : ℕ) - (omitProd p o' * ∏ j, Z' j : ℕ) : ℝ) *
        (∏ j, T j : ℕ) * r)
open scoped Classical in
/-- Test (ii) of PD §3.2 at the ratio `r`: for every nonempty set `I` of groups, with
`i_* = max I`, the fresh draws outside `I` failing `Separated` have probability at most
`exp(-L^{a_{i_*}} / 4)`. -/
def GoodSecond (x : ℝ) (d : Data K) (d₀ : ℝ) {J : ℕ} (r : ℝ) (p : Lists K J) : Prop :=
  ∀ I : Finset (Fin K), ∀ hI : I.Nonempty,
    ∑ T ∈ (freshDraws x d I).filter (fun T => ¬ Separated x d d₀ I (I.max' hI) r p T),
        freshWeight x d I T ≤
      Real.exp (-Real.log x ^ d.a (I.max' hI) / 4)

/-! ### Operators -/

/-! ### Pairings and the moment -/
/-- The state measure `∏_i V_i^{-M}`. -/
def stateMass (x : ℝ) (d : Data K) : ℝ := (d.bandMass x)⁻¹ ^ (padCount x + 1)

end Erdos408.OneSided

end
end
end

-- ==== Examples.plasma_ai__erdos_408.Dependencies.v2536eee0f99d.Erdos408.OneSided.Model ====
public section
set_option autoImplicit false
/-!
# Position models

The lift of PD §3.2 over an abstract set of positions (`blueprint/one_sided_type_ii.md` §11).
A position model has:

* a finite type of positions;
* a determinant `det : Pos → Pos → ℤ`;
* a divisibility predicate `FirstDvd p P` ("`p` divides the first coordinate of `P`");
* a ratio `ratio P` (the `r_P` of the good-state tests).

The row operation, the symmetrization, the good-state projection, the operator `𝒜` and the
moment at a base position are defined once, for every model. Two instances matter:

* `physModel`: the primitive positions of `Ω`, with `p ∣ P₁` and `r_P`. Its operators are
  those of `Lift.lean` (`detMoment_eq_sum_moment`).
* `rootModel`: at a real root `ϱ = (u, v, r)` and lines `ℓ`, the primitive `z ∈ ℤ²` with
  `g(ϱ) z ∈ Ω`. Here `p ∣ (gz)₁` is replaced by `[z]_p = ℓ_p`, and `r_{gz}` by
  `τ(w_z)/τ(z)`, where `τ(z) = z₁ + r z₂` and `w_z` is a complement of `z`. PD Lemma 3.4
  compares the physical moment with the average of root moments over independent uniform
  lines.

The good-state tests are invariant under adding an integer to the ratio, so models are
compared with ratios modulo `ℤ`.
-/
@[expose] public section
noncomputable section
namespace Erdos408.OneSided
open Finset Real
open scoped Matrix
variable {K : ℕ}
/-- A position model: finitely many positions, with a determinant, divisibility of the first
coordinate, and the ratio used by the good-state tests. -/
structure PosModel where
  /-- The positions. -/
  Pos : Type
  [instFintype : Fintype Pos]
  [instDecEq : DecidableEq Pos]
  /-- The determinant of two positions. -/
  det : Pos → Pos → ℤ
  /-- `p` divides the first coordinate of the position. -/
  FirstDvd : ℕ → Pos → Prop
  /-- The ratio `r_P`. -/
  ratio : Pos → ℝ
attribute [instance] PosModel.instFintype PosModel.instDecEq
namespace PosModel
variable (M : PosModel)
open scoped Classical in
/-- The states: a position and lists whose labels all divide its first coordinate. -/
def states (x : ℝ) (d : Data K) : Finset (M.Pos × Lists K (padCount x)) :=
  (univ ×ˢ lists x d (padCount x)).filter fun s => ∀ i h, M.FirstDvd (s.2 i h) s.1
/-- The state space of the model. -/
abbrev State (x : ℝ) (d : Data K) := ↥(M.states x d)
open scoped Classical in
/-- `ω(P)`: the number of band primes dividing the first coordinate. -/
def bandCount (x : ℝ) (d : Data K) (P : M.Pos) : ℕ :=
  ∑ i, ((band x (d.a i)).filter fun p => M.FirstDvd p P).card
open scoped Classical in
/-- The row operation `𝒯` of PD §3.2 over the model; see `Erdos408.OneSided.rowOp`. -/
def rowOp (q A₀ x : ℝ) (d : Data K) (Y d₀ : ℝ) :
    Matrix (M.State x d) (M.State x d) ℂ := fun s s' =>
  if (∀ i (h : Fin (padCount x)), s'.1.2 i h.castSucc = s.1.2 i h.castSucc) ∧
      (∀ i i' h', s'.1.2 i (Fin.last _) ≠ s.1.2 i' h') ∧
      d₀ ≤ (padProd s.1.2 : ℝ) ∧ (padProd s.1.2 : ℝ) < 2 * d₀ ∧
      (padProd s.1.2 : ℤ) ∣ M.det s.1.1 s'.1.1 then
    (((d.bandMass x)⁻¹ * (d₀ / padProd s.1.2) * dyadicBump (lastProd s.1.2 / Y) *
        dyadicBump (lastProd s'.1.2 / Y) *
        plateau ((M.det s.1.1 s'.1.1 / padProd s.1.2 : ℤ) / Y) *
        q ^ (((M.bandCount x d s.1.1 : ℝ) - K * (padCount x + 1)) / 2 +
          ((M.bandCount x d s'.1.1 : ℝ) - K * (padCount x + 1)) / 2) : ℝ) : ℂ) *
      ((if M.det s.1.1 s'.1.1 / padProd s.1.2 = (lastProd s.1.2 : ℤ) - lastProd s'.1.2 then 1
          else 0) -
        arcIntegral A₀ x Y
          (M.det s.1.1 s'.1.1 / padProd s.1.2 - lastProd s.1.2 + lastProd s'.1.2))
  else 0
open scoped Classical in
/-- The slot symmetrization `𝒮` over the model. -/
def symOp (x : ℝ) (d : Data K) : Matrix (M.State x d) (M.State x d) ℂ := fun s s' =>
  if s.1.1 = s'.1.1 ∧
      ∃ σ : Fin K → Equiv.Perm (Fin (padCount x + 1)), ∀ i, s'.1.2 i = s.1.2 i ∘ σ i then
    (((padCount x + 1).factorial ^ K : ℕ) : ℂ)⁻¹
  else 0

end PosModel
/-! ### Reindexing along an equivalence of states -/
section Reindex
variable {α β : Type*} [Fintype α] [Fintype β]

end Reindex
/-! ### Integer shifts of the ratio -/

/-! ### The moments over base positions -/

/-! ### Isomorphisms of models -/

namespace PosModel.Iso
variable {M N : PosModel} 

end PosModel.Iso

/-! ### The physical model -/

/-! ### The model at a real root -/
/-- `τ(z) = z₁ + r z₂`. -/
def tau (r : ℝ) (z : ℤ × ℤ) : ℝ := z.1 + r * z.2
/-- A complement of `z`, from Bézout: `det(z, w_z) = gcd(z₁, z₂)`. -/
def complement (z : ℤ × ℤ) : ℤ × ℤ := (-Int.gcdB z.1 z.2, Int.gcdA z.1 z.2)

/-- A bound for the positions at a root: every `z` with `g(ϱ) z ∈ Ω` has
`|z₁|, |z₂| ≤ 2 (16U + 2V + 1)²`. -/
def rootBound (U V : ℝ) : ℕ := ⌈2 * (16 * U + 2 * V + 1) ^ 2⌉₊
/-- The primitive `z` with `g(ϱ) z ∈ Ω`, where `g(ϱ) = (u, ur; v, vr + 1/u)`, so that
`(g z)₁ = u τ(z)` and `(g z)₂ = v τ(z) + z₂/u`. -/
def rootPositions (U V u v r : ℝ) : Finset (ℤ × ℤ) :=
  ((Icc (-(rootBound U V : ℤ)) (rootBound U V)) ×ˢ
      (Icc (-(rootBound U V : ℤ)) (rootBound U V))).filter fun z =>
    Int.gcd z.1 z.2 = 1 ∧ U ≤ u * tau r z ∧ u * tau r z ≤ 16 * U ∧
      V ≤ v * tau r z + z.2 / u ∧ v * tau r z + z.2 / u ≤ 2 * V

end Erdos408.OneSided

end
end
end

-- ==== Examples.plasma_ai__erdos_408.Dependencies.v2536eee0f99d.Erdos408.OneSided.Moment.RootReplacement.Config ====
public section
set_option autoImplicit false
/-!
# Configurations: the path expansion over a root-independent index set

RR2 of `blueprint/one_sided_type_ii.md` §15, in the form used by the root replacement. The
fixed-line path expansion `rootMoment_eq_sum_lineFactor` sums over paths of states of
`freeRootModel` at the root `ϱ = (u, v, r)`, whose positions depend on `ϱ`. All of them lie
in the square `|z₁|, |z₂| ≤ rootBound U V`, which depends only on `U = d₀ Y H_m` and
`V = H_n`. A *configuration* is a path of `N + 1` states over this square
(`squareModel`). Then

`rootMoment(ϱ, ℓ) = ∑_ω c(ω) · A(ω, ϱ) · ∏_p λ_p(ω, ℓ_p)`  (`rootMoment_eq_sum_conf`),

where

* `confCoeff` is the root-independent coefficient `c(ω)`: the state mass, the endpoint
  condition `z₀ = z_N = e₁`, and the kernel `𝒮 𝒯 𝒮` at `q = 1` along the path;
* `confInd` is the archimedean indicator `A(ω, ϱ)`: every visit is a position at `ϱ`
  (the box) and passes both good-state tests at the transported ratio `τ(w_z)/τ(z)`;
* `confLineFactor` is the line factor `λ_p`, as `lineFactor`.

The primes of the lists along `ω` are `confActive ω`; at every other band prime the line
factor is the damping `∏_j (1 - η'_j [ℓ = [z_j]_p])`.

The line-free states at `ϱ` include into the square states (`toSquare`), onto the states at a
position at `ϱ`. Along the inclusion, the line-free edge operator is `g (𝒮 𝒯 𝒮) g`, with `g`
the visit indicator (`freeRootModel_edgeOp_eq`), so the weight of a path is `c(ω) A(ω, ϱ)`
up to the mass and endpoint condition (`pathWeight_eq_prod_confKernel`). The configurations
with a visit off the positions at `ϱ` have `A(ω, ϱ) = 0`.
-/
@[expose] public section
noncomputable section
namespace Erdos408.OneSided
open Finset Real
open scoped Matrix
variable {K : ℕ}
/-- The square `|z₁|, |z₂| ≤ rootBound U V`, which contains the positions at every root. -/
def rootSquare (U V : ℝ) : Finset (ℤ × ℤ) :=
  Icc (-(rootBound U V : ℤ)) (rootBound U V) ×ˢ Icc (-(rootBound U V : ℤ)) (rootBound U V)
/-- The square model: the points of `rootSquare`, with every prime dividing. Its ratio is
never used. -/
def squareModel (d : Data K) (Y d₀ : ℝ) : PosModel where
  Pos := ↥(rootSquare (d₀ * Y * d.Hm) d.Hn)
  det z z' := z.1.1 * z'.1.2 - z.1.2 * z'.1.1
  FirstDvd _ _ := True
  ratio _ := 0
/-- The configurations: paths of `N + 1` states of the square model, `N = 2R`. -/
abbrev Conf (x : ℝ) (d : Data K) (Y d₀ : ℝ) :=
  Fin (2 * momentPower x + 1) → (squareModel d Y d₀).State x d
/-- The root-free kernel `𝒮 𝒯 𝒮` of the square model at `q = 1`. -/
def confKernel (A₀ x : ℝ) (d : Data K) (Y d₀ : ℝ) :
    Matrix ((squareModel d Y d₀).State x d) ((squareModel d Y d₀).State x d) ℂ :=
  (squareModel d Y d₀).symOp x d * (squareModel d Y d₀).rowOp 1 A₀ x d Y d₀ *
    (squareModel d Y d₀).symOp x d
/-- The coefficient `c(ω)`: the state mass, the endpoint condition `z₀ = z_N = e₁`, and the
kernel `𝒮 𝒯 𝒮` along the path. It does not depend on the root. -/
def confCoeff (A₀ x : ℝ) (d : Data K) (Y d₀ : ℝ) (ω : Conf x d Y d₀) : ℂ :=
  (stateMass x d : ℂ) *
    (if (ω 0).1.1.1 = (1, 0) ∧ (ω (Fin.last _)).1.1.1 = (1, 0) then 1 else 0) *
    ∏ j : Fin (2 * momentPower x), confKernel A₀ x d Y d₀ (ω j.castSucc) (ω j.succ)
/-- The transported ratio `τ(w_z)/τ(z)` at the ratio `r`, the ratio of `rootModel`. -/
def rootRatioAt (r : ℝ) (z : ℤ × ℤ) : ℝ := tau r (complement z) / tau r z
open scoped Classical in
/-- The indicator of one visit at the root `ϱ = (u, v, r)`: the point is a position at `ϱ`
and the state passes both good-state tests at the transported ratio. -/
def visitInd (x : ℝ) (d : Data K) (Y d₀ u v r : ℝ) (s : (squareModel d Y d₀).State x d) : ℝ :=
  if s.1.1.1 ∈ rootPositions (d₀ * Y * d.Hm) d.Hn u v r ∧
      GoodFirst Y d₀ (rootRatioAt r s.1.1.1) s.1.2 ∧
      GoodSecond x d d₀ (rootRatioAt r s.1.1.1) s.1.2 then 1
  else 0
/-- The archimedean indicator `A(ω, ϱ)`: the product of the visit indicators. -/
def confInd (x : ℝ) (d : Data K) (Y d₀ : ℝ) (ω : Conf x d Y d₀) (u v r : ℝ) : ℝ :=
  ∏ j, visitInd x d Y d₀ u v r (ω j)

/-- A configuration is live when its indicator is nonzero at some root of the box
`[U, 16U] × [V, 2V] × [0, 1]`. Only live configurations contribute to the root
replacement. -/
def ConfLive {x : ℝ} {d : Data K} {Y d₀ : ℝ} (ω : Conf x d Y d₀) : Prop :=
  ∃ u v r : ℝ, d₀ * Y * d.Hm ≤ u ∧ u ≤ 16 * (d₀ * Y * d.Hm) ∧ d.Hn ≤ v ∧ v ≤ 2 * d.Hn ∧
    0 ≤ r ∧ r ≤ 1 ∧ confInd x d Y d₀ ω u v r ≠ 0
/-! ### Elementary bounds -/

/-! ### The line-free states among the square states -/
section Square
variable {d : Data K} {Y d₀ u v r x : ℝ}

end Square
/-! ### The expansion over configurations -/

end Erdos408.OneSided

end
end
end

-- ==== Examples.plasma_ai__erdos_408.Examples.Example_b69fef6bf3ec3c959f27_Tube ====
set_option autoImplicit false
/-!
# The tube

PD `det:tube` ((3.30), §3.5), for the configurations of `Config.lean`. A configuration with
`c(ω) ≠ 0` starts at `e₁`, its consecutive determinants are below `10 H`, `H = d₀ Y`, since
the pad product `D ∈ [d₀, 2d₀)` divides `det(z, z')` and the plateau forces
`|det(z, z')/D| < 5Y`, and `d₀, Y` are below the product of the labels, since `D ≥ d₀` and the
bump `η(b/Y)` forces `b > Y`.

If moreover the configuration is live, all its visits are positions at one root `ϱ` of the
box. Then `g z_j ∈ Ω` and `det(g z, g z') = det(z, z')`, so consecutive slopes of `g z_j`
differ by at most `10 H / U²`, and `z_{j,2} = det(g e₁, g z_j)` is at most `2560 N H`
(`tube_of_live`). Since `τ(z_j) ∈ [1/16, 16]`, also `|z_{j,1}| ≤ 2560 N H + 16`.
-/
@[expose] public section
noncomputable section
namespace Erdos408.OneSided
open Finset Real
variable {K : ℕ}
/-! ### Nonzero entries of the operators -/

/-! ### Slopes in the box -/
/-- Points `P_j = (A_j, B_j)`, `j ≤ N`, with `A_j ∈ [U, 16U]` and consecutive determinants at
most `10 H` have `|det(P₀, P_j)| ≤ 2560 N H`: consecutive slopes differ by at most
`10 H / U²`, and `det(P₀, P_j) = A₀ A_j (B_j / A_j - B₀ / A₀)`. -/
axiom abs_det_le_of_consecutive {N : ℕ} {U H : ℝ} (hU : 0 < U) (hH : 0 ≤ H)
    (A B : Fin (N + 1) → ℝ) (hA : ∀ j, U ≤ A j ∧ A j ≤ 16 * U)
    (hdet : ∀ j : Fin N, |A j.castSucc * B j.succ - B j.castSucc * A j.succ| ≤ 10 * H)
    (j : Fin (N + 1)) : |A 0 * B j - B 0 * A j| ≤ 2560 * N * H
/-- `c(ω) ≠ 0` forces the start `z₀ = e₁`, consecutive determinants below `10 d₀ Y`, and
`d₀ ≤ ∏ labels`, `Y < ∏ labels` for the labels of the first state. -/
axiom confCoeff_ne_zero_imp {A₀ x : ℝ} {d : Data K} {Y d₀ : ℝ} (hY : 0 < Y) (hd₀ : 0 < d₀)
    (hR : 0 < momentPower x) {ω : Conf x d Y d₀} (hc : confCoeff A₀ x d Y d₀ ω ≠ 0) :
    (ω 0).1.1.1 = (1, 0) ∧
      (∀ j : Fin (2 * momentPower x),
        |(((ω j.castSucc).1.1.1.1 * (ω j.succ).1.1.1.2 -
            (ω j.castSucc).1.1.1.2 * (ω j.succ).1.1.1.1 : ℤ) : ℝ)| < 10 * d₀ * Y) ∧
      d₀ ≤ listProd (ω 0).1.2 ∧ Y < listProd (ω 0).1.2
/-- **The tube** (`det:tube`): a live configuration with `c(ω) ≠ 0` has
`|z_{j,2}| ≤ 2560 N H` and `|z_{j,1}| ≤ 2560 N H + 16` at every visit, `H = d₀ Y`. -/
theorem tube_of_live {A₀ x : ℝ} {d : Data K} {Y d₀ : ℝ} (hY : 0 < Y) (hd₀ : 0 < d₀)
    (hHm : 0 < d.Hm) (hR : 0 < momentPower x) {ω : Conf x d Y d₀}
    (hc : confCoeff A₀ x d Y d₀ ω ≠ 0) (hω : ConfLive ω) (j : Fin (2 * momentPower x + 1)) :
    |((ω j).1.1.1.2 : ℝ)| ≤ 2560 * (2 * momentPower x) * (d₀ * Y) ∧
      |((ω j).1.1.1.1 : ℝ)| ≤ 2560 * (2 * momentPower x) * (d₀ * Y) + 16 := by
  classical
  obtain ⟨hz₀, hdet, -⟩ := confCoeff_ne_zero_imp hY hd₀ hR hc
  obtain ⟨u, v, r, hu₁, hu₂, -, -, hr₀, hr₁, hind⟩ := hω
  have hU : 0 < d₀ * Y * d.Hm := by positivity
  have hu : 0 < u := hU.trans_le hu₁
  -- step: every visit is a position at the root `(u, v, r)`
  have hvis : ∀ i, d₀ * Y * d.Hm ≤ u * tau r (ω i).1.1.1 ∧
      u * tau r (ω i).1.1.1 ≤ 16 * (d₀ * Y * d.Hm) := by
    intro i
    have hi := (prod_ne_zero_iff.1 hind) i (mem_univ _)
    unfold visitInd at hi
    obtain ⟨-, h₁, h₂, -⟩ := (mem_filter.1 (ite_ne_right_iff.1 hi).1.1).2
    exact ⟨h₁, h₂⟩
  -- step: `g z ∈ Ω` and `det(g z, g z') = det(z, z')`
  set A : Fin (2 * momentPower x + 1) → ℝ := fun i => u * tau r (ω i).1.1.1
  set B : Fin (2 * momentPower x + 1) → ℝ :=
    fun i => v * tau r (ω i).1.1.1 + ((ω i).1.1.1.2 : ℝ) / u
  have hid : ∀ i k, A i * B k - B i * A k =
      ((ω i).1.1.1.1 : ℝ) * (ω k).1.1.1.2 - ((ω i).1.1.1.2 : ℝ) * (ω k).1.1.1.1 := by
    intro i k
    simp only [A, B, tau]
    field_simp
    ring
  have h₂ := abs_det_le_of_consecutive hU (by positivity : 0 ≤ d₀ * Y) A B
    (fun i => ⟨(hvis i).1, by linarith [(hvis i).2]⟩) (fun i => by
      rw [hid]
      have := hdet i
      push_cast at this
      linarith) j
  rw [hid, hz₀] at h₂
  simp only [Int.cast_one, Int.cast_zero, one_mul, zero_mul, sub_zero] at h₂
  have h₂' : |((ω j).1.1.1.2 : ℝ)| ≤ 2560 * (2 * momentPower x) * (d₀ * Y) := by
    push_cast at h₂
    linarith
  refine ⟨h₂', ?_⟩
  -- step: `τ(z_j) ∈ (0, 16]`, and `z_{j,1} = τ(z_j) - r z_{j,2}`
  have hτ₀ : 0 < tau r (ω j).1.1.1 := pos_of_mul_pos_right (hU.trans_le (hvis j).1) hu.le
  have hτ₁ : tau r (ω j).1.1.1 ≤ 16 := by
    by_contra h
    push Not at h
    have := (hvis j).2
    nlinarith
  have hrz : |r * ((ω j).1.1.1.2 : ℝ)| ≤ |((ω j).1.1.1.2 : ℝ)| := by
    rw [abs_mul, abs_of_nonneg hr₀]
    exact mul_le_of_le_one_left (abs_nonneg _) hr₁
  have heq : ((ω j).1.1.1.1 : ℝ) = tau r (ω j).1.1.1 - r * (ω j).1.1.1.2 := by
    simp only [tau]
    ring
  rw [heq]
  calc |tau r (ω j).1.1.1 - r * ((ω j).1.1.1.2 : ℝ)|
      ≤ |tau r (ω j).1.1.1| + |r * ((ω j).1.1.1.2 : ℝ)| := abs_sub _ _
    _ ≤ 16 + 2560 * (2 * momentPower x) * (d₀ * Y) := by
        rw [abs_of_pos hτ₀]
        linarith
    _ = 2560 * (2 * momentPower x) * (d₀ * Y) + 16 := by ring
end Erdos408.OneSided
