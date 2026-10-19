/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.GroupScheme.ClosureMap
import PadicHodge.GroupScheme.QuotientPoints
import PadicHodge.GroupScheme.DiscriminantChain
import PadicHodge.GroupScheme.Faithful
import PadicHodge.FormalGroup.GenericIso

/-!
# Closures of a `p`-divisible subgroup of the generic fibre ([Hong, proof of Prop. 3.5.3])

Let `R` be a local PID with fraction field `K`, `G = (G_v)` a `p`-divisible group over `R` and
`ι : H̃ → G_K` a homomorphism of `p`-divisible groups over `K` whose levels `ι_v : H̃_v ↪ G_{v,K}`
are closed immersions. Let `H_v ⊆ G_v` be the scheme-theoretic closure of `H̃_v`
(`Hom.clo ι v`). Following [Hong, proof of Prop. 3.5.3]:

* the inclusions and quotient maps of `G` restrict to the closures (`cloIncl`, `cloQuot`), with
  `cloIncl ∘ cloQuot = [p]` and `cloQuot ∘ cloIncl = [p]` on points; `|H_v| = p^{hv}`
  (`order_clo`), `H_v(Ω) ≅ H̃_v(Ω)` for a separably closed `K`-algebra `Ω`;
* the quotients `Q_v = H_{v+1}/H_v` have order `p^h` (`order_Q`), and `quot` induces
  `δ_v : Q_{v+1} → Q_v` (`delta`), bijective on `Ω`-points (`delta_mapPoints_bijective`; in
  [Hong] `δ_v` is induced by `[p]`, here directly by `quot`), hence after `Ω ⊗_R -`;
* **stabilisation** (`exists_delta_bijective`): `δ_v` is an isomorphism for `v ≫ 0`.
  Deviation from [Hong] (which uses the noetherianity of the integral closure of `R` in
  `K ⊗ O(Q_1)`, adapting [AM, Prop. 5.17]): `disc(Q_v) ⊆ disc(Q_{v+1})`
  (`discIdeal_le_of_bijective_baseChange`) is an ascending chain of ideals of the noetherian `R`,
  and equal nonzero discriminants force `δ_v` to be bijective (`bijective_of_discIdeal_eq`).

## References

* [Hong] S. Hong, *Notes on p-adic Hodge theory*, proof of Prop. 3.5.3.
-/

noncomputable section

open Coalgebra HopfAlgebra WithConv TensorProduct

namespace PadicHodge

universe u

namespace PDivGroup

open FFGroupScheme

variable {R : Type u} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] {K : Type u} [Field K]
  [Algebra R K] [IsFractionRing R K] {p : ℕ} {G : PDivGroup R p} {H : PDivGroup K p}

attribute [local instance] FFGroupScheme.algebraBase

omit [IsDomain R] [IsPrincipalIdealRing R] in
variable (R K) in
theorem algebraMap_injective_of_isFractionRing (Ω : Type*) [Field Ω] [Algebra K Ω]
    [Algebra R Ω] [IsScalarTower R K Ω] : Function.Injective (algebraMap R Ω) := by
  rw [IsScalarTower.algebraMap_eq R K Ω]
  exact (algebraMap K Ω).injective.comp (IsFractionRing.injective R K)

namespace Hom

variable (ι : Hom H (G.baseChange K))

/-! ### The closures `H_v` and their transition maps -/

/-- The closure `H_v` of `H̃_v` in `G_v`. -/
abbrev clo (v : ℕ) : FFGroupScheme R := (ι.f v).closure

/-- The closed immersion `H_v → G_v`. -/
abbrev cloHom (v : ℕ) : FFGroupScheme.Hom (ι.clo v) (G.G v) := (ι.f v).closureHom

omit [IsPrincipalIdealRing R] [IsFractionRing R K] in
theorem incl_cond (v : ℕ) (a : (G.G (v + 1)).A) :
    ι.f v (1 ⊗ₜ G.incl v a) = H.incl v (ι.f (v + 1) (1 ⊗ₜ a)) :=
  (congrArg (fun φ : (G.baseChange K).G (v + 1) |>.A →ₐc[K] (H.G v).A => φ (1 ⊗ₜ a))
    (ι.comm v)).symm

omit [IsPrincipalIdealRing R] [IsFractionRing R K] in
theorem quot_cond (v : ℕ) (a : (G.G v).A) :
    ι.f (v + 1) (1 ⊗ₜ G.quot v a) = H.quot v (ι.f v (1 ⊗ₜ a)) := by
  let T := (H.G (v + 1)).A
  have claim : (G.quot v).mapPoints T ((G.G (v + 1)).baseChangePointsEquiv (S := K) T
      ((ι.f (v + 1)).mapPoints T (H.G (v + 1)).univPt)) =
      (G.G v).baseChangePointsEquiv (S := K) T
        ((ι.f v).mapPoints T ((H.quot v).mapPoints T (H.G (v + 1)).univPt)) := by
    apply G.mapPoints_injective v T
    rw [G.incl_quot]
    change _ = (G.G (v + 1)).baseChangePointsEquiv (S := K) T
      (((G.baseChange K).incl v).mapPoints T ((ι.f v).mapPoints T
        ((H.quot v).mapPoints T (H.G (v + 1)).univPt)))
    rw [ι.incl_mapPoints, H.incl_quot, map_pow]
    exact (map_pow _ _ _).symm
  exact congrArg (fun z : (G.G v).points T => ofConv z a) claim

/-- The closed immersion `H_v → H_{v+1}` (restriction of `i_v`). -/
def cloIncl (v : ℕ) : FFGroupScheme.Hom (ι.clo v) (ι.clo (v + 1)) :=
  FFGroupScheme.Hom.closureInduced (ι.f v) (ι.f (v + 1)) (G.incl v) (H.incl v) (ι.incl_cond v)

/-- The map `H_{v+1} → H_v` (restriction of `quot_v`). -/
def cloQuot (v : ℕ) : FFGroupScheme.Hom (ι.clo (v + 1)) (ι.clo v) :=
  FFGroupScheme.Hom.closureInduced (ι.f (v + 1)) (ι.f v) (G.quot v) (H.quot v) (ι.quot_cond v)

theorem cloIncl_surjective (v : ℕ) : Function.Surjective (ι.cloIncl v) :=
  FFGroupScheme.Hom.closureInduced_surjective _ _ _ _ _ (G.incl_surjective v)

theorem cloHom_injective (v : ℕ) {T : Type*} [CommRing T] [Algebra R T] :
    Function.Injective ((ι.cloHom v).mapPoints T) :=
  FFGroupScheme.Hom.mapPoints_injective_of_surjective (ι.f v).closureHom_surjective

theorem cloIncl_injective (v : ℕ) {T : Type*} [CommRing T] [Algebra R T] :
    Function.Injective ((ι.cloIncl v).mapPoints T) :=
  FFGroupScheme.Hom.mapPoints_injective_of_surjective (ι.cloIncl_surjective v)

theorem cloHom_cloIncl (v : ℕ) {T : Type*} [CommRing T] [Algebra R T]
    (z : (ι.clo v).points T) :
    (ι.cloHom (v + 1)).mapPoints T ((ι.cloIncl v).mapPoints T z) =
      (G.incl v).mapPoints T ((ι.cloHom v).mapPoints T z) := rfl

theorem cloHom_cloQuot (v : ℕ) {T : Type*} [CommRing T] [Algebra R T]
    (z : (ι.clo (v + 1)).points T) :
    (ι.cloHom v).mapPoints T ((ι.cloQuot v).mapPoints T z) =
      (G.quot v).mapPoints T ((ι.cloHom (v + 1)).mapPoints T z) := rfl

/-- `cloIncl ∘ cloQuot = [p]` on points. -/
theorem cloIncl_cloQuot (v : ℕ) {T : Type*} [CommRing T] [Algebra R T]
    (z : (ι.clo (v + 1)).points T) :
    (ι.cloIncl v).mapPoints T ((ι.cloQuot v).mapPoints T z) = z ^ p := by
  apply ι.cloHom_injective (v + 1)
  rw [cloHom_cloIncl, cloHom_cloQuot, G.incl_quot, map_pow]

/-- `cloQuot ∘ cloIncl = [p]` on points. -/
theorem cloQuot_cloIncl (v : ℕ) {T : Type*} [CommRing T] [Algebra R T]
    (z : (ι.clo (v + 1)).points T) :
    (ι.cloQuot (v + 1)).mapPoints T ((ι.cloIncl (v + 1)).mapPoints T z) = z ^ p := by
  apply ι.cloIncl_injective (v + 1)
  rw [cloIncl_cloQuot, map_pow]

/-- `H_v` is killed by `p^v`. -/
theorem clo_killedBy (v : ℕ) : (ι.clo v).KilledBy (p ^ v) :=
  KilledBy.of_injective (ι.cloHom v) (fun _ _ _ => ι.cloHom_injective v)
    (KilledBy.of_pow_eq_one fun S _ _ x => G.pow_eq_one v S x)

/-- **`|H_v| = p^{hv}`.** -/
theorem order_clo (hι : ∀ v, Function.Surjective (ι.f v)) (v : ℕ) :
    (ι.clo v).order = p ^ (H.height * v) :=
  ((ι.f v).order_closure (hι v)).trans (H.order_eq v)

/-! ### Points over a separably closed field -/

section Points

variable (Ω : Type u) [Field Ω] [IsSepClosed Ω] [Algebra K Ω] [Algebra R Ω]
  [IsScalarTower R K Ω]

omit [IsSepClosed Ω] in
theorem cloQuot_closurePt (v : ℕ) (y : (H.G (v + 1)).points Ω) :
    (ι.cloQuot v).mapPoints Ω ((ι.f (v + 1)).closurePt Ω y) =
      (ι.f v).closurePt Ω ((H.quot v).mapPoints Ω y) :=
  FFGroupScheme.Hom.closureInduced_closurePt _ _ _ _ _ _ _

omit [IsSepClosed Ω] in
theorem cloIncl_closurePt (v : ℕ) (y : (H.G v).points Ω) :
    (ι.cloIncl v).mapPoints Ω ((ι.f v).closurePt Ω y) =
      (ι.f (v + 1)).closurePt Ω ((H.incl v).mapPoints Ω y) :=
  FFGroupScheme.Hom.closureInduced_closurePt _ _ _ _ _ _ _

variable [Fact p.Prime] (hpΩ : (p : Ω) ≠ 0) (hι : ∀ v, Function.Surjective (ι.f v))

include hpΩ hι

omit [Fact p.Prime] in
theorem card_clo_points (v : ℕ) : Nat.card ((ι.clo v).points Ω) = p ^ (H.height * v) := by
  rw [← Nat.card_congr ((ι.f v).closurePtEquiv Ω (hι v)).toEquiv]
  exact H.card_points_sepClosed Ω hpΩ v

theorem cloQuot_surjective_points (v : ℕ) :
    Function.Surjective ((ι.cloQuot v).mapPoints Ω) := by
  intro z
  obtain ⟨y, rfl⟩ := ((ι.f v).closurePt_bijective Ω (hι v)).2 z
  obtain ⟨y', rfl⟩ := H.quot_surjective_sepClosed Ω hpΩ v y
  exact ⟨_, ι.cloQuot_closurePt Ω v y'⟩

end Points

/-! ### The quotients `Q_v = H_{v+1}/H_v` -/

/-- `Q_v = H_{v+1}/H_v`. -/
abbrev Q (v : ℕ) : FFGroupScheme R := (ι.cloIncl v).quotient

/-- `H_{v+1} → Q_v`. -/
abbrev piQ (v : ℕ) : FFGroupScheme.Hom (ι.clo (v + 1)) (ι.Q v) := (ι.cloIncl v).quotientHom

theorem delta_cond (v : ℕ) (a : (ι.clo (v + 1)).A) :
    ι.cloIncl (v + 1) (ι.cloQuot (v + 1) a) = ι.cloQuot v (ι.cloIncl v a) := by
  have : (ι.cloIncl (v + 1)).comp (ι.cloQuot (v + 1)) = (ι.cloQuot v).comp (ι.cloIncl v) :=
    FFGroupScheme.Hom.ext_points fun S _ _ z => by
      change (ι.cloQuot (v + 1)).mapPoints S ((ι.cloIncl (v + 1)).mapPoints S z) =
        (ι.cloIncl v).mapPoints S ((ι.cloQuot v).mapPoints S z)
      rw [cloQuot_cloIncl, cloIncl_cloQuot]
  exact congrArg (fun φ : (ι.clo (v + 1)).A →ₐc[R] (ι.clo (v + 1)).A => φ a) this

/-- **`δ_v : Q_{v+1} → Q_v`**, induced by `quot_{v+1} : H_{v+2} → H_{v+1}`. -/
def delta (v : ℕ) : FFGroupScheme.Hom (ι.Q (v + 1)) (ι.Q v) :=
  FFGroupScheme.Hom.quotientMap (ι.cloIncl (v + 1)) (ι.cloIncl v) (ι.cloQuot (v + 1))
    (ι.cloQuot v) (ι.delta_cond v)

theorem delta_piQ (v : ℕ) {T : Type*} [CommRing T] [Algebra R T]
    (z : (ι.clo (v + 2)).points T) :
    (ι.delta v).mapPoints T ((ι.piQ (v + 1)).mapPoints T z) =
      (ι.piQ v).mapPoints T ((ι.cloQuot (v + 1)).mapPoints T z) := rfl

/-- `Q_v` is killed by `p^{v+1}`. -/
theorem Q_killedBy (v : ℕ) : (ι.Q v).KilledBy (p ^ (v + 1)) :=
  KilledBy.quotient _ (ι.clo_killedBy (v + 1))

section Order

variable [IsLocalRing R] [Fact p.Prime] (hι : ∀ v, Function.Surjective (ι.f v))

include hι

/-- **`|Q_v| = p^h`.** -/
theorem order_Q (v : ℕ) : (ι.Q v).order = p ^ H.height := by
  have h := FFGroupScheme.Hom.order_eq_mul (ι.cloIncl_surjective v)
  rw [ι.order_clo hι, ι.order_clo hι, mul_add, mul_one, pow_add] at h
  exact (Nat.eq_of_mul_eq_mul_left (pow_pos (Fact.out : p.Prime).pos _) h).symm

variable (Ω : Type u) [Field Ω] [IsSepClosed Ω] [Algebra K Ω] [Algebra R Ω]
  [IsScalarTower R K Ω] (hpΩ : (p : Ω) ≠ 0)

include hpΩ

omit [IsLocalRing R] [Fact p.Prime] hι [IsSepClosed Ω] [Algebra K Ω] [IsScalarTower R K Ω] in
theorem Q_isEtale (v : ℕ) : ((ι.Q v).baseChange Ω).IsEtale :=
  (ι.Q_killedBy v).isEtale_baseChange Ω (by rw [Nat.cast_pow]; exact pow_ne_zero _ hpΩ)

omit [Algebra K Ω] [IsScalarTower R K Ω] in
theorem card_Q_points (v : ℕ) : Nat.card ((ι.Q v).points Ω) = p ^ H.height := by
  rw [(ι.Q_killedBy v).card_points Ω (by rw [Nat.cast_pow]; exact pow_ne_zero _ hpΩ),
    ι.order_Q hι]

theorem piQ_surjective_points (v : ℕ) : Function.Surjective ((ι.piQ v).mapPoints Ω) := by
  refine FFGroupScheme.Hom.quotientHom_mapPoints_surjective (ι.cloIncl_surjective v) Ω ?_ ?_ ?_ ?_
  · rw [ι.card_clo_points Ω hpΩ hι, ι.order_clo hι]
  · rw [ι.card_clo_points Ω hpΩ hι, ι.order_clo hι]
  · rw [ι.card_Q_points hι Ω hpΩ, ι.order_Q hι]
  · rw [ι.order_clo hι]
    exact pow_ne_zero _ (Fact.out : p.Prime).ne_zero

/-- **`δ_v` is bijective on `Ω`-points.** -/
theorem delta_mapPoints_bijective (v : ℕ) : Function.Bijective ((ι.delta v).mapPoints Ω) := by
  have hsurj : Function.Surjective ((ι.delta v).mapPoints Ω) := by
    intro q
    obtain ⟨z, rfl⟩ := ι.piQ_surjective_points hι Ω hpΩ v q
    obtain ⟨w, rfl⟩ := ι.cloQuot_surjective_points Ω hpΩ hι (v + 1) z
    exact ⟨_, ι.delta_piQ v w⟩
  have hfin : Finite ((ι.Q (v + 1)).points Ω) := by
    refine Nat.finite_of_card_ne_zero ?_
    rw [ι.card_Q_points hι Ω hpΩ]
    exact pow_ne_zero _ (Fact.out : p.Prime).ne_zero
  refine hsurj.bijective_of_nat_card_le ?_
  rw [ι.card_Q_points hι Ω hpΩ, ι.card_Q_points hι Ω hpΩ]

/-- `Ω ⊗ δ_v` is bijective. -/
theorem delta_baseChange_bijective (v : ℕ) :
    Function.Bijective (Algebra.TensorProduct.map (AlgHom.id Ω Ω)
      (ι.delta v : (ι.Q v).A →ₐ[R] (ι.Q (v + 1)).A)) :=
  FFGroupScheme.bijective_baseChange_of_mapPoints Ω (ι.delta v) (ι.Q_isEtale Ω hpΩ (v + 1))
    (ι.Q_isEtale Ω hpΩ v) (ι.delta_mapPoints_bijective hι Ω hpΩ v)

theorem discIdeal_Q_le (v : ℕ) : discIdeal R (ι.Q v).A ≤ discIdeal R (ι.Q (v + 1)).A :=
  discIdeal_le_of_bijective_baseChange Ω
    (by change (ι.Q (v + 1)).order = (ι.Q v).order; rw [ι.order_Q hι, ι.order_Q hι])
    (algebraMap_injective_of_isFractionRing R K Ω) _ (ι.delta_baseChange_bijective hι Ω hpΩ v)

/-- **Stabilisation**: `δ_v` is an isomorphism for all `v ≥ v₀`. -/
theorem exists_delta_bijective : ∃ v₀, ∀ v, v₀ ≤ v → Function.Bijective (ι.delta v) := by
  let f : ℕ →o Ideal R := ⟨fun v => discIdeal R (ι.Q v).A,
    monotone_nat_of_le_succ fun v => ι.discIdeal_Q_le hι Ω hpΩ v⟩
  obtain ⟨n, hn⟩ := monotone_stabilizes_iff_noetherian.mpr (inferInstance : IsNoetherian R R) f
  refine ⟨n, fun v hv => ?_⟩
  have hd : discIdeal R (ι.Q (v + 1)).A = discIdeal R (ι.Q v).A :=
    ((hn (v + 1) (by omega)).symm.trans (hn v hv) :)
  have : Algebra.Etale Ω (Ω ⊗[R] (ι.Q v).A) := ι.Q_isEtale Ω hpΩ v
  exact bijective_of_discIdeal_eq Ω
    (by change (ι.Q (v + 1)).order = (ι.Q v).order; rw [ι.order_Q hι, ι.order_Q hι])
    (algebraMap_injective_of_isFractionRing R K Ω)
    (ι.delta v : (ι.Q v).A →ₐ[R] (ι.Q (v + 1)).A) (ι.delta_baseChange_bijective hι Ω hpΩ v) hd
    (discIdeal_ne_bot_of_etale Ω)

end Order

end Hom

end PDivGroup

end PadicHodge
