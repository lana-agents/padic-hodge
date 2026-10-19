/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.GroupScheme.ClosurePDiv
import PadicHodge.GroupScheme.TateFree

/-!
# [Hong, Prop. 3.5.3]: extending a `p`-divisible subgroup of the generic fibre

Let `R` be a local PID with fraction field `K`, `Ω` a separably closed `K`-algebra field with
`p ≠ 0`, `G` a `p`-divisible group over `R` and `ι : H̃ → G_K` a homomorphism of `p`-divisible
groups over `K` with closed immersions `ι_v : H̃_v ↪ G_{v,K}`. With the closures `H_v ⊆ G_v`, the
quotients `Q_v = H_{v+1}/H_v` and `v₀` such that `δ_v : Q_{v+1} → Q_v` is an isomorphism for
`v ≥ v₀` (`ClosurePDiv.lean`), [Hong, proof of Prop. 3.5.3] sets `H'_v = H_{v₀+v}/H_{v₀}`:

* `subPDiv`: `(H'_v)` with the closed immersions `H'_v → H'_{v+1}` (`subQuot`) is a
  `p`-divisible group of height `h(H̃)`; the kernel condition `H'_{v+1}[p^v] = H'_v` comes from
  `[p^v] = j ∘ Δ ∘ quotQuot` on `H'_{v+1}` (`pow_eq_j_Delta`) with `Δ = δ_{v₀} ∘ ⋯ ∘ δ_{v₀+v-1}`
  an isomorphism (`Delta_bijective`), `j : Q_{v₀} → H'_{v+1}` a closed immersion and the third
  isomorphism theorem (`mapPoints_quotQuot_eq_one_iff`);
* `subPDivHom : H' → G`, `H'_v = H_{v₀+v}/H_{v₀} → H_v → G_v` induced by `[p^{v₀}]`
  (iterated `quot`, `quotientLift`);
* **`exists_pdivGroup_closure`** ([Hong, Prop. 3.5.3], generic-fibre form): there are a
  `p`-divisible group `H'` over `R` of height `h(H̃)` and `ι' : H' → G` which is `ι` on
  `Ω`-points at every level, through isomorphisms `H'_v(Ω) ≅ H̃_v(Ω)`.

In [Hong] the input is a `Γ_K`-stable direct summand `M ⊆ T_p G`, turned into `H̃` by
[Hong, Prop. 2.1.14]; that Galois-descent step is in `GroupScheme/SummandPDiv.lean`
(`exists_tateSub_of_isCompl`, and `exists_pdivGroup_of_isCompl` for Prop. 3.5.3 in its original
form). It is not needed for [Hong, Thm. 3.5.4], where `H̃_v` is the graph of `f̃_v`.

## References

* [Hong] S. Hong, *Notes on p-adic Hodge theory*, Prop. 3.5.3 and its proof.
-/

noncomputable section

open Coalgebra HopfAlgebra WithConv TensorProduct

namespace PadicHodge

universe u

namespace FFGroupScheme

variable {R : Type u} [CommRing R]

theorem Hom.mapPoints_comp {G H X : FFGroupScheme R} (f : Hom G H) (g : Hom H X) {S : Type*}
    [CommRing S] [Algebra R S] (z : G.points S) :
    Hom.mapPoints (f.comp g : Hom G X) S z = g.mapPoints S (f.mapPoints S z) := rfl

theorem Hom.mapPoints_id {G : FFGroupScheme R} {S : Type*} [CommRing S] [Algebra R S]
    (z : G.points S) : Hom.mapPoints (BialgHom.id R G.A : Hom G G) S z = z := rfl

/-- An endomorphism of `G/H` which is `x ↦ x^n` on the image of the universal point of `G` is
`x ↦ x^n`. -/
theorem Hom.mapPoints_eq_pow_of_quotient [IsDomain R] [IsPrincipalIdealRing R]
    {G H : FFGroupScheme R} (i : Hom H G) (Φ : Hom i.quotient i.quotient) (n : ℕ)
    (h : Φ.mapPoints G.A (i.quotientHom.mapPoints G.A G.univPt) =
      (i.quotientHom.mapPoints G.A G.univPt) ^ n)
    {S : Type*} [CommRing S] [Algebra R S] (y : i.quotient.points S) :
    Φ.mapPoints S y = y ^ n := by
  have h1 : Φ.mapPoints _ i.quotient.univPt = i.quotient.univPt ^ n := by
    apply i.quotient.postComp_injective (φ := (i.quotientHom : i.quotient.A →ₐ[R] G.A))
      (Hom.quotientHom_injective i)
    rw [map_pow]
    exact h
  have := congrArg (i.quotient.postComp (ofConv y)) h1
  rw [map_pow] at this
  exact this

end FFGroupScheme

namespace PDivGroup

open FFGroupScheme

variable {R : Type u} [CommRing R] {p : ℕ}

/-- `quot_{b+1} ∘ i_{b+1} = i_b ∘ quot_b` on points. -/
theorem quot_incl (G : PDivGroup R p) (b : ℕ) {S : Type u} [CommRing S] [Algebra R S]
    (y : (G.G (b + 1)).points S) :
    (G.quot (b + 1)).mapPoints S ((G.incl (b + 1)).mapPoints S y) =
      (G.incl b).mapPoints S ((G.quot b).mapPoints S y) := by
  apply G.mapPoints_injective (b + 1) S
  rw [G.incl_quot, G.incl_quot, map_pow]

/-- `quotLE` commutes with the inclusions. -/
theorem quotLE_incl (G : PDivGroup R p) (S : Type u) [CommRing S] [Algebra R S] {a b : ℕ}
    (h : a ≤ b) (h' : a + 1 ≤ b + 1) (y : (G.G b).points S) :
    G.quotLE S h' ((G.incl b).mapPoints S y) = (G.incl a).mapPoints S (G.quotLE S h y) := by
  induction b, h using Nat.le_induction with
  | base => rw [quotLE_self, quotLE_self]
  | succ b hb ih =>
    rw [G.quotLE_succ S (by omega : a + 1 ≤ b + 1), G.quot_incl, ih (by omega),
      G.quotLE_succ S hb]

variable [IsDomain R] [IsPrincipalIdealRing R] {K : Type u} [Field K] [Algebra R K]
  [IsFractionRing R K] {G : PDivGroup R p} {H : PDivGroup K p}

attribute [local instance] FFGroupScheme.algebraBase

namespace Hom

variable (ι : Hom H (G.baseChange K))

/-! ### Iterated maps between the closures -/

/-- The iterated quotient map `H_b → H_a` for `a ≤ b`. -/
def cloQuotLE {a b : ℕ} (h : a ≤ b) : FFGroupScheme.Hom (ι.clo b) (ι.clo a) :=
  Nat.leRecOn (C := fun k => FFGroupScheme.Hom (ι.clo k) (ι.clo a)) h
    (fun {k} f => (ι.cloQuot k).comp f) (BialgHom.id R _)

theorem cloQuotLE_self (a : ℕ) : ι.cloQuotLE (le_refl a) = BialgHom.id R _ := by
  rw [cloQuotLE, Nat.leRecOn_self]

theorem cloQuotLE_succ {a b : ℕ} (h : a ≤ b) (h' : a ≤ b + 1) :
    ι.cloQuotLE h' = (ι.cloQuot b).comp (ι.cloQuotLE h) := by
  rw [cloQuotLE, Nat.leRecOn_succ h]
  rfl

/-- `H_b → H_a → G_a` is `H_b → G_b → G_a`. -/
theorem cloHom_cloQuotLE {a b : ℕ} (h : a ≤ b) {T : Type u} [CommRing T] [Algebra R T]
    (z : (ι.clo b).points T) :
    (ι.cloHom a).mapPoints T ((ι.cloQuotLE h).mapPoints T z) =
      G.quotLE T h ((ι.cloHom b).mapPoints T z) := by
  induction b, h using Nat.le_induction with
  | base => rw [cloQuotLE_self, quotLE_self]; rfl
  | succ b hb ih =>
    rw [ι.cloQuotLE_succ hb, FFGroupScheme.Hom.mapPoints_comp, ih, G.quotLE_succ T hb,
      cloHom_cloQuot]

/-- `cloQuotLE` is `quotLE` of `H̃` on the points of the generic fibre. -/
theorem cloQuotLE_closurePt (Ω : Type u) [Field Ω] [Algebra K Ω] [Algebra R Ω]
    [IsScalarTower R K Ω] {a b : ℕ} (h : a ≤ b) (y : (H.G b).points Ω) :
    (ι.cloQuotLE h).mapPoints Ω ((ι.f b).closurePt Ω y) =
      (ι.f a).closurePt Ω (H.quotLE Ω h y) := by
  induction b, h using Nat.le_induction with
  | base => rw [cloQuotLE_self, quotLE_self]; rfl
  | succ b hb ih =>
    rw [ι.cloQuotLE_succ hb, FFGroupScheme.Hom.mapPoints_comp, cloQuot_closurePt, ih,
      H.quotLE_succ Ω hb]

variable (v₀ : ℕ)

/-- The iterated inclusion `H_{v₀} → H_{v₀+v}`. -/
def kk : (v : ℕ) → FFGroupScheme.Hom (ι.clo v₀) (ι.clo (v₀ + v))
  | 0 => BialgHom.id R _
  | v + 1 => (kk v).comp (ι.cloIncl (v₀ + v))

theorem kk_surjective : ∀ v, Function.Surjective (ι.kk v₀ v)
  | 0 => Function.surjective_id
  | v + 1 => (kk_surjective v).comp (ι.cloIncl_surjective (v₀ + v))

/-- The iterated quotient map `H_{v₀+v+1} → H_{v₀+1}`. -/
def quotUp : (v : ℕ) → FFGroupScheme.Hom (ι.clo (v₀ + v + 1)) (ι.clo (v₀ + 1))
  | 0 => BialgHom.id R _
  | v + 1 => (ι.cloQuot (v₀ + (v + 1))).comp (quotUp v)

/-- The iterated inclusion `H_{v₀+1} → H_{v₀+v+1}`. -/
def inclUp : (v : ℕ) → FFGroupScheme.Hom (ι.clo (v₀ + 1)) (ι.clo (v₀ + v + 1))
  | 0 => BialgHom.id R _
  | v + 1 => (inclUp v).comp (ι.cloIncl (v₀ + v + 1))

theorem inclUp_surjective : ∀ v, Function.Surjective (ι.inclUp v₀ v)
  | 0 => Function.surjective_id
  | v + 1 => (inclUp_surjective v).comp (ι.cloIncl_surjective (v₀ + v + 1))

/-- `inclUp ∘ quotUp = [p^v]` on points. -/
theorem inclUp_quotUp (v : ℕ) {T : Type*} [CommRing T] [Algebra R T]
    (z : (ι.clo (v₀ + v + 1)).points T) :
    (ι.inclUp v₀ v).mapPoints T ((ι.quotUp v₀ v).mapPoints T z) = z ^ (p ^ v) := by
  induction v with
  | zero => rw [pow_zero, pow_one]; rfl
  | succ v ih =>
    change (ι.cloIncl (v₀ + v + 1)).mapPoints T ((ι.inclUp v₀ v).mapPoints T
      ((ι.quotUp v₀ v).mapPoints T ((ι.cloQuot (v₀ + v + 1)).mapPoints T z))) = _
    rw [ih, map_pow, cloIncl_cloQuot, ← pow_mul, ← pow_succ']

theorem kk_succ_apply (v : ℕ) (a : (ι.clo (v₀ + (v + 1))).A) :
    ι.kk v₀ (v + 1) a = ι.cloIncl v₀ (ι.inclUp v₀ v a) := by
  induction v with
  | zero => rfl
  | succ v ih => exact ih (ι.cloIncl (v₀ + v + 1) a)

/-! ### The `p`-divisible group `H'_v = H_{v₀+v}/H_{v₀}` -/

/-- `H'_v = H_{v₀+v}/H_{v₀}`. -/
abbrev Hp (v : ℕ) : FFGroupScheme R := (ι.kk v₀ v).quotient

/-- `H_{v₀+v} → H'_v`. -/
abbrev piH (v : ℕ) : FFGroupScheme.Hom (ι.clo (v₀ + v)) (ι.Hp v₀ v) :=
  (ι.kk v₀ v).quotientHom

/-- The closed immersion `H'_v → H'_{v+1}`. -/
def inclH (v : ℕ) : FFGroupScheme.Hom (ι.Hp v₀ v) (ι.Hp v₀ (v + 1)) :=
  FFGroupScheme.Hom.subQuot (ι.cloIncl (v₀ + v)) (ι.kk v₀ v)

/-- `H'_{v+1} → Q_{v₀+v} = H_{v₀+v+1}/H_{v₀+v}`. -/
def QQ (v : ℕ) : FFGroupScheme.Hom (ι.Hp v₀ (v + 1)) (ι.Q (v₀ + v)) :=
  FFGroupScheme.Hom.quotQuot (ι.cloIncl (v₀ + v)) (ι.kk v₀ v)

/-- `Δ_v = δ_{v₀} ∘ ⋯ ∘ δ_{v₀+v-1} : Q_{v₀+v} → Q_{v₀}`. -/
def Delta : (v : ℕ) → FFGroupScheme.Hom (ι.Q (v₀ + v)) (ι.Q v₀)
  | 0 => BialgHom.id R _
  | v + 1 => (ι.delta (v₀ + v)).comp (Delta v)

theorem Delta_piQ (v : ℕ) {T : Type*} [CommRing T] [Algebra R T]
    (z : (ι.clo (v₀ + v + 1)).points T) :
    (ι.Delta v₀ v).mapPoints T ((ι.piQ (v₀ + v)).mapPoints T z) =
      (ι.piQ v₀).mapPoints T ((ι.quotUp v₀ v).mapPoints T z) := by
  induction v with
  | zero => rfl
  | succ v ih => exact ih ((ι.cloQuot (v₀ + (v + 1))).mapPoints T z)

/-- `j : Q_{v₀} = H_{v₀+1}/H_{v₀} → H_{v₀+v+1}/H_{v₀} = H'_{v+1}`. -/
def jj (v : ℕ) : FFGroupScheme.Hom (ι.Q v₀) (ι.Hp v₀ (v + 1)) :=
  FFGroupScheme.Hom.quotientMap (ι.cloIncl v₀) (ι.kk v₀ (v + 1)) (ι.inclUp v₀ v)
    (BialgHom.id R _) fun a => (ι.kk_succ_apply v₀ v a).symm

theorem jj_injective (v : ℕ) [IsLocalRing R] {T : Type*} [CommRing T] [Algebra R T] :
    Function.Injective ((ι.jj v₀ v).mapPoints T) :=
  FFGroupScheme.Hom.mapPoints_injective_of_surjective
    (FFGroupScheme.Hom.surjective_quotientMap_of_comp (ι.inclUp_surjective v₀ v)
      (ι.cloIncl_surjective v₀) _)

/-- **`[p^v] = j ∘ Δ ∘ quotQuot` on `H'_{v+1}`** ([Hong, proof of Prop. 3.5.3], the
commutative diagram). -/
theorem pow_eq_jj_Delta (v : ℕ) {S : Type*} [CommRing S] [Algebra R S]
    (y : (ι.Hp v₀ (v + 1)).points S) :
    y ^ (p ^ v) =
      (ι.jj v₀ v).mapPoints S ((ι.Delta v₀ v).mapPoints S ((ι.QQ v₀ v).mapPoints S y)) := by
  symm
  refine FFGroupScheme.Hom.mapPoints_eq_pow_of_quotient (ι.kk v₀ (v + 1))
    ((ι.QQ v₀ v).comp ((ι.Delta v₀ v).comp (ι.jj v₀ v))) (p ^ v) ?_ y
  change (ι.jj v₀ v).mapPoints _ ((ι.Delta v₀ v).mapPoints _
    ((ι.piQ (v₀ + v)).mapPoints _ (ι.clo (v₀ + (v + 1))).univPt)) = _
  rw [Delta_piQ]
  change (ι.piH v₀ (v + 1)).mapPoints _ ((ι.inclUp v₀ v).mapPoints _
    ((ι.quotUp v₀ v).mapPoints _ (ι.clo (v₀ + (v + 1))).univPt)) = _
  rw [inclUp_quotUp, map_pow]

variable [IsLocalRing R] (hv₀ : ∀ v, v₀ ≤ v → Function.Bijective (ι.delta v))

omit [IsLocalRing R] in
include hv₀ in
theorem Delta_bijective : ∀ v, Function.Bijective (ι.Delta v₀ v)
  | 0 => Function.bijective_id
  | v + 1 => (hv₀ (v₀ + v) (by omega)).comp (Delta_bijective v)

include hv₀ in
/-- **The kernel condition** for `H'`: `H'_{v+1}[p^v] = H'_v`. -/
theorem Hp_range_eq (v : ℕ) {S : Type*} [CommRing S] [Algebra R S]
    (y : (ι.Hp v₀ (v + 1)).points S) :
    (∃ x, (ι.inclH v₀ v).mapPoints S x = y) ↔ y ^ (p ^ v) = 1 := by
  refine (FFGroupScheme.Hom.mapPoints_quotQuot_eq_one_iff (ι.cloIncl_surjective (v₀ + v))
    (ι.kk_surjective v₀ v) (S := S) y).symm.trans ?_
  change (ι.QQ v₀ v).mapPoints S y = 1 ↔ _
  rw [ι.pow_eq_jj_Delta v₀ v]
  constructor
  · intro h
    rw [h, map_one, map_one]
  · intro h
    apply (FFGroupScheme.Hom.mapPoints_bijective _ (ι.Delta_bijective v₀ hv₀ v) S).1
    apply ι.jj_injective v₀ v
    rw [h, map_one, map_one]

variable [Fact p.Prime] (hι : ∀ v, Function.Surjective (ι.f v))

include hι in
theorem order_Hp (v : ℕ) : (ι.Hp v₀ v).order = p ^ (H.height * v) := by
  have h := FFGroupScheme.Hom.order_eq_mul (ι.kk_surjective v₀ v)
  rw [ι.order_clo hι, ι.order_clo hι, mul_add, pow_add] at h
  exact (Nat.eq_of_mul_eq_mul_left (pow_pos (Fact.out : p.Prime).pos _) h).symm

/-- **The `p`-divisible group `H' = (H_{v₀+v}/H_{v₀})_v`** ([Hong, proof of Prop. 3.5.3]). -/
def subPDiv : PDivGroup R p where
  height := H.height
  G := ι.Hp v₀
  order_eq := ι.order_Hp v₀ hι
  incl := ι.inclH v₀
  incl_surjective v := FFGroupScheme.Hom.surjective_subQuot (ι.cloIncl_surjective (v₀ + v))
    (ι.kk_surjective v₀ v)
  range_eq v _ _ _ y := ι.Hp_range_eq v₀ hv₀ v y

/-! ### The homomorphism `H' → G` -/

omit [IsLocalRing R] [Fact p.Prime] in
theorem kk_cloQuotLE_trivial (v : ℕ) (x : (ι.clo v).A) :
    ι.kk v₀ v (ι.cloQuotLE (Nat.le_add_left v v₀) x) =
      algebraMap R (ι.clo v₀).A (counit (R := R) x) := by
  refine FFGroupScheme.Hom.trivial_of_mapPoints (ι.kk v₀ v) _ (fun S _ _ z => ?_) x
  apply ι.cloHom_injective v
  rw [cloHom_cloQuotLE, map_one, quotLE_eq_one_iff, show v₀ + v - v = v₀ by omega, ← map_pow,
    ← map_pow, (ι.clo_killedBy v₀).pow_eq_one, map_one, map_one]

/-- `H'_v = H_{v₀+v}/H_{v₀} → H_v`, induced by `[p^{v₀}]`. -/
def psi (v : ℕ) : FFGroupScheme.Hom (ι.Hp v₀ v) (ι.clo v) :=
  FFGroupScheme.Hom.quotientLift (ι.kk v₀ v) (ι.cloQuotLE (Nat.le_add_left v v₀))
    (ι.kk_cloQuotLE_trivial v₀ v)

omit [IsLocalRing R] [Fact p.Prime] in
theorem psi_piH (v : ℕ) {T : Type*} [CommRing T] [Algebra R T]
    (z : (ι.clo (v₀ + v)).points T) :
    (ι.psi v₀ v).mapPoints T ((ι.piH v₀ v).mapPoints T z) =
      (ι.cloQuotLE (Nat.le_add_left v v₀)).mapPoints T z := rfl

/-- `ι'_v : H'_v → H_v → G_v`. -/
def subPDivHom : Hom (ι.subPDiv v₀ hv₀ hι) G where
  f v := (ι.psi v₀ v).comp (ι.cloHom v)
  comm v := by
    refine FFGroupScheme.Hom.ext_quotient (ι.kk v₀ v) fun S _ _ z => ?_
    change (ι.cloHom (v + 1)).mapPoints S ((ι.cloQuotLE (Nat.le_add_left (v + 1) v₀)).mapPoints S
        ((ι.cloIncl (v₀ + v)).mapPoints S z)) =
      (G.incl v).mapPoints S ((ι.cloHom v).mapPoints S
        ((ι.cloQuotLE (Nat.le_add_left v v₀)).mapPoints S z))
    rw [cloHom_cloQuotLE, cloHom_cloQuotLE]
    change G.quotLE S _ ((ι.cloHom (v₀ + v + 1)).mapPoints S
      ((ι.cloIncl (v₀ + v)).mapPoints S z)) = _
    rw [cloHom_cloIncl]
    exact G.quotLE_incl S _ _ _

/-! ### Points over `Ω` -/

variable (Ω : Type u) [Field Ω] [IsSepClosed Ω] [Algebra K Ω] [Algebra R Ω]
  [IsScalarTower R K Ω] (hpΩ : (p : Ω) ≠ 0)

omit hv₀ in
include hpΩ hι in
theorem psi_bijective_points (v : ℕ) : Function.Bijective ((ι.psi v₀ v).mapPoints Ω) := by
  have hsurj : Function.Surjective ((ι.psi v₀ v).mapPoints Ω) := by
    intro w
    obtain ⟨y, rfl⟩ := ((ι.f v).closurePt_bijective Ω (hι v)).2 w
    obtain ⟨t, rfl⟩ := H.proj_surjective_sepClosed Ω hpΩ v y
    refine ⟨(ι.piH v₀ v).mapPoints Ω ((ι.f (v₀ + v)).closurePt Ω (t.1 (v₀ + v))), ?_⟩
    rw [psi_piH, cloQuotLE_closurePt, TateModule.quotLE_apply]
    rfl
  have hn : ((p ^ (v₀ + v) : ℕ) : Ω) ≠ 0 := by rw [Nat.cast_pow]; exact pow_ne_zero _ hpΩ
  have hcard : Nat.card ((ι.Hp v₀ v).points Ω) = p ^ (H.height * v) := by
    rw [(KilledBy.quotient (ι.kk v₀ v) (ι.clo_killedBy (v₀ + v))).card_points Ω hn,
      ι.order_Hp v₀ hι]
  have hfin : Finite ((ι.Hp v₀ v).points Ω) := by
    refine Nat.finite_of_card_ne_zero ?_
    rw [hcard]
    exact pow_ne_zero _ (Fact.out : p.Prime).ne_zero
  refine hsurj.bijective_of_nat_card_le ?_
  rw [hcard, ι.card_clo_points Ω hpΩ hι]

include hpΩ in
/-- **`ι'` is `ι` on `Ω`-points**, through `H'_v(Ω) ≅ H_v(Ω) ≅ H̃_v(Ω)`. -/
theorem exists_subPDivHom_points (v : ℕ) :
    ∃ e : ((ι.subPDiv v₀ hv₀ hι).G v).points Ω ≃* (H.G v).points Ω,
      ∀ x, ((ι.subPDivHom v₀ hv₀ hι).f v).mapPoints Ω x =
        (G.G v).baseChangePointsEquiv Ω ((ι.f v).mapPoints Ω (e x)) := by
  let e1 := MulEquiv.ofBijective ((ι.psi v₀ v).mapPoints Ω) (ι.psi_bijective_points v₀ hι Ω hpΩ v)
  let e2 := (ι.f v).closurePtEquiv Ω (hι v)
  refine ⟨e1.trans e2.symm, fun x => ?_⟩
  change (ι.cloHom v).mapPoints Ω (e1 x) = _
  have : e1 x = e2 (e2.symm (e1 x)) := (e2.apply_symm_apply _).symm
  rw [this]
  exact (ι.f v).closureHom_closurePt Ω _

end Hom

/-- **[Hong, Prop. 3.5.3]** (generic-fibre form). Let `R` be a local PID with fraction field `K`,
`Ω` a separably closed field over `K` with `p ≠ 0`, `G` a `p`-divisible group over `R` and
`ι : H̃ → G_K` a homomorphism of `p`-divisible groups over `K` whose levels are closed immersions.
Then there are a `p`-divisible group `H'` over `R` of height `h(H̃)` and a homomorphism
`ι' : H' → G` which, at every level, is `ι` on `Ω`-points through an isomorphism
`H'_v(Ω) ≅ H̃_v(Ω)`. -/
theorem Hom.exists_pdivGroup_closure [IsLocalRing R] [Fact p.Prime] (ι : Hom H (G.baseChange K))
    (hι : ∀ v, Function.Surjective (ι.f v)) (Ω : Type u) [Field Ω] [IsSepClosed Ω] [Algebra K Ω]
    [Algebra R Ω] [IsScalarTower R K Ω] (hpΩ : (p : Ω) ≠ 0) :
    ∃ (H' : PDivGroup R p) (ι' : Hom H' G), H'.height = H.height ∧
      ∀ v, ∃ e : (H'.G v).points Ω ≃* (H.G v).points Ω,
        ∀ x, (ι'.f v).mapPoints Ω x =
          (G.G v).baseChangePointsEquiv Ω ((ι.f v).mapPoints Ω (e x)) := by
  obtain ⟨v₀, hv₀⟩ := ι.exists_delta_bijective hι Ω hpΩ
  exact ⟨ι.subPDiv v₀ hv₀ hι, ι.subPDivHom v₀ hv₀ hι, rfl,
    ι.exists_subPDivHom_points v₀ hv₀ hι Ω hpΩ⟩

end PDivGroup

end PadicHodge
