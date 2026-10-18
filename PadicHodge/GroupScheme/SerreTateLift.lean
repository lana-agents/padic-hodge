/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.GroupScheme.SerreTatePDiv
import PadicHodge.GroupScheme.BaseChange

/-!
# Serre–Tate, essential surjectivity: lifting coordinates from the special fibre

Let `H = (G_v, i_v)` be a `p`-divisible group over a coefficient ring `R` (`SerreTate.CoeffRing`,
e.g. `ℤ_p`, `O_{K'}`) with layers `A_v`, and `k` a field with
`R ↠ k` of kernel `𝔪` (the residue field). **Special-fibre data** (`SpecialFibreData H k d`)
are surjective `k`-algebra maps `ρ̄_v : k[[t_1, …, t_d]] ↠ k ⊗ A_v`, compatible with the
transition maps, with `ker ρ̄_v ⊆ (t_j^{p^v})_j` ([Hong, Prop. 2.2.13]: `lim_v (A_v ⊗ k) ≅
k[[t]]`, proved for the special fibre in `GroupScheme/SerreTateSpecial.lean`).

Following [Hong, Thm. 2.2.16, proof]:

* `tmul_eq_zero_iff`: `ker(A_v → k ⊗ A_v) = 𝔪 A_v` (`A_v` free);
* `SpecialFibreData.liftSeq`: compatible lifts `y_v ∈ A_v^d` of `ρ̄_v(t)` ("choose
  `y_1, …, y_d ∈ A_{v+1}` lifting … correcting by `z_i ∈ 𝔪A_{v+1}`"), normalised to `ε(y_v) = 0`
  (`SpecialFibreData.Y`); they are topologically nilpotent since `k ⊗ A_v` is artinian local;
* `SpecialFibreData.ev_surjective`: `f_v : R[[t]] → A_v` is surjective (Nakayama);
* `SpecialFibreData.eq_zero`: `⋂_v ker f_v = 0` (reduction modulo `𝔪`,
  `SerreTate.eq_zero_of_forall_red`; this replaces Hong's splitting argument);
* **`SpecialFibreData.coords`**, and **`exists_iso_of_specialFibre`**: `H ≅ F[p^∞]` for a
  `p`-divisible formal group law `F` ([Hong, Thm. 2.2.16], essential surjectivity), given the
  special-fibre data.
-/

noncomputable section

open MvPowerSeries IsLocalRing PadicHodge.AdicEval TensorProduct WithConv

namespace PadicHodge

namespace SerreTate

variable {R : Type} [CommRing R] [IsLocalRing R]
  {p : ℕ}

local notation "𝔪p" => maximalIdeal R

attribute [local instance] PDivFGL.isAdicComplete_free

/-! ### Reduction of free modules -/

section Red

variable {k : Type} [Field k] [Algebra R k]
  (hker : ∀ r : R, algebraMap R k r = 0 ↔ r ∈ maximalIdeal R)
include hker

/-- **`ker(A → k ⊗ A) = 𝔪 A`** for a finite free `R`-algebra `A`. -/
theorem tmul_eq_zero_iff {A : Type} [CommRing A] [Algebra R A] [Module.Free R A]
    [Module.Finite R A] (a : A) :
    (1 : k) ⊗ₜ[R] a = 0 ↔ a ∈ (𝔪p).map (algebraMap R A) := by
  classical
  let b := Module.Free.chooseBasis R A
  constructor
  · intro h
    have hr : ∀ i, b.repr a i ∈ 𝔪p := fun i => by
      have := congrArg (fun x => (Algebra.TensorProduct.basis k b).repr x i) h
      simp only [Algebra.TensorProduct.basis_repr_tmul, one_smul, Finsupp.mapRange_apply,
        map_zero, Finsupp.coe_zero, Pi.zero_apply] at this
      exact (hker _).mp this
    rw [← b.sum_repr a]
    refine Ideal.sum_mem _ fun i _ => ?_
    rw [Algebra.smul_def]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (hr i))
  · intro h
    have hle : (𝔪p).map (algebraMap R A) ≤
        RingHom.ker (Algebra.TensorProduct.includeRight (R := R) (A := k) (B := A)) := by
      rw [Ideal.map_le_iff_le_comap]
      intro r hr
      rw [Ideal.mem_comap, RingHom.mem_ker, AlgHom.commutes,
        Algebra.TensorProduct.algebraMap_apply, (hker r).mpr hr, TensorProduct.zero_tmul]
    exact hle h

end Red

/-- **Special-fibre data** for `H`: coordinates `ρ̄_v : k[[t]] ↠ k ⊗ A_v` of the special fibre,
compatible with the transition maps, with `ker ρ̄_v ⊆ (t_j^{p^v})_j` ([Hong, Prop. 2.2.13]). -/
structure SpecialFibreData (H : PDivGroup R p) (k : Type) [Field k] [Algebra R k]
    (d : ℕ) where
  /-- the coordinates of the special fibre -/
  ρ : ∀ v, MvPowerSeries (Fin d) k →ₐ[k] k ⊗[R] (H.G v).A
  surj : ∀ v, Function.Surjective (ρ v)
  compat : ∀ v g, FFGroupScheme.baseChangeHom k (H.incl v) (ρ (v + 1) g) = ρ v g
  ker_le : ∀ v, RingHom.ker (ρ v) ≤ spanXPow (Fin d) k (p ^ v)

namespace SpecialFibreData

variable {H : PDivGroup R p} {k : Type} [Field k] [Algebra R k] {d : ℕ}
  (S : SpecialFibreData H k d)

/-- `A_v → k ⊗ A_v`. -/
abbrev π (v : ℕ) : (H.G v).A →ₐ[R] k ⊗[R] (H.G v).A :=
  Algebra.TensorProduct.includeRight

omit [IsLocalRing R] in
theorem π_incl (v : ℕ) (a : (H.G (v + 1)).A) :
    π (k := k) v (H.incl v a) = FFGroupScheme.baseChangeHom k (H.incl v) (π (v + 1) a) := rfl

omit [IsLocalRing R] in
/-- **`ρ̄_v(t_j)` is nilpotent**: `k ⊗ A_v` is artinian local. -/
theorem exists_pow_eq_zero (v : ℕ) (j : Fin d) : ∃ N, S.ρ v (X j) ^ N = 0 := by
  rcases subsingleton_or_nontrivial (k ⊗[R] (H.G v).A) with h | h
  · exact ⟨1, Subsingleton.elim _ _⟩
  haveI : IsLocalRing (k ⊗[R] (H.G v).A) :=
    IsLocalRing.of_surjective' (S.ρ v).toRingHom (S.surj v)
  haveI : IsArtinianRing (k ⊗[R] (H.G v).A) := IsArtinianRing.of_finite k _
  obtain ⟨n, hn⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := k ⊗[R] (H.G v).A)
  rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top] at hn
  refine ⟨n, ?_⟩
  have hm : S.ρ v (X j) ∈ maximalIdeal (k ⊗[R] (H.G v).A) := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    haveI : IsLocalHom (S.ρ v).toRingHom := IsLocalHom.of_surjective _ (S.surj v)
    have := (isUnit_map_iff (S.ρ v).toRingHom (X j)).mp hu
    rw [MvPowerSeries.isUnit_iff_constantCoeff, constantCoeff_X] at this
    exact not_isUnit_zero this
  have := Ideal.pow_mem_pow hm n
  rwa [hn, Ideal.zero_eq_bot, Ideal.mem_bot] at this

variable (hsurj : Function.Surjective (algebraMap R k))
  (hker : ∀ r : R, algebraMap R k r = 0 ↔ r ∈ maximalIdeal R)

omit [IsLocalRing R] in
include hsurj in
theorem π_surjective (v : ℕ) : Function.Surjective (π (H := H) (k := k) v) := by
  intro x
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | tmul s a =>
    obtain ⟨r, rfl⟩ := hsurj s
    refine ⟨r • a, ?_⟩
    rw [Algebra.TensorProduct.includeRight_apply, TensorProduct.tmul_smul,
      Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul']
  | add x x' hx hx' =>
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨a', rfl⟩ := hx'
    exact ⟨a + a', map_add _ _ _⟩

include hker in
theorem π_eq_zero_iff (v : ℕ) (a : (H.G v).A) :
    π (k := k) v a = 0 ↔ a ∈ (𝔪p).map (algebraMap R (H.G v).A) :=
  tmul_eq_zero_iff hker a

/-- Lifts of `ρ̄_v(t)` to `A_v`. -/
abbrev Lifts (v : ℕ) : Type := {y : Fin d → (H.G v).A // ∀ j, π v (y j) = S.ρ v (X j)}

include hsurj hker in
/-- **The lifting step** ([Hong, Thm. 2.2.16, proof]): a lift at level `v` extends to a lift at
level `v + 1`. -/
theorem exists_lift_succ (v : ℕ) (y : S.Lifts v) :
    ∃ y' : S.Lifts (v + 1), ∀ j, H.incl v (y'.1 j) = y.1 j := by
  choose ŷ hŷ using fun j => π_surjective (H := H) hsurj (v + 1) (S.ρ (v + 1) (X j))
  have hdiff : ∀ j, H.incl v (ŷ j) - y.1 j ∈ (𝔪p).map (algebraMap R (H.G v).A) := by
    intro j
    rw [← π_eq_zero_iff hker, map_sub, π_incl, hŷ, S.compat, y.2, sub_self]
  have hmap : (𝔪p).map (algebraMap R (H.G v).A) ≤
      ((𝔪p).map (algebraMap R (H.G (v + 1)).A)).map (H.incl v) :=
    Ideal.map_le_iff_le_comap.mpr fun r hr => by
      rw [Ideal.mem_comap, ← AlgHomClass.commutes (H.incl v) r]
      exact Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ hr)
  have hz : ∀ j, ∃ z ∈ (𝔪p).map (algebraMap R (H.G (v + 1)).A),
      H.incl v z = H.incl v (ŷ j) - y.1 j := fun j =>
    (Ideal.mem_map_iff_of_surjective _ (H.incl_surjective v)).mp (hmap (hdiff j))
  choose z hz hzv using hz
  refine ⟨⟨fun j => ŷ j - z j, fun j => ?_⟩, fun j => ?_⟩
  · rw [map_sub, hŷ, (π_eq_zero_iff hker _ _).mpr (hz j), sub_zero]
  · simp only [map_sub, hzv, sub_sub_cancel]

omit [IsLocalRing R] in
include hsurj in
theorem exists_lift_zero : Nonempty (S.Lifts 0) :=
  ⟨⟨fun j => (π_surjective hsurj 0 (S.ρ 0 (X j))).choose,
    fun j => (π_surjective hsurj 0 (S.ρ 0 (X j))).choose_spec⟩⟩

/-- **Compatible lifts** `y_v` of `ρ̄_v(t)`. -/
def liftSeq : ∀ v, S.Lifts v
  | 0 => (S.exists_lift_zero hsurj).some
  | v + 1 => (S.exists_lift_succ hsurj hker v (liftSeq v)).choose

theorem incl_liftSeq (v : ℕ) (j : Fin d) :
    H.incl v ((S.liftSeq hsurj hker (v + 1)).1 j) = (S.liftSeq hsurj hker v).1 j :=
  (S.exists_lift_succ hsurj hker v (S.liftSeq hsurj hker v)).choose_spec j

/-- The normalised lifts `y_v - ε(y_v)`. -/
def Y (v : ℕ) (j : Fin d) : (H.G v).A :=
  (S.liftSeq hsurj hker v).1 j -
    algebraMap R _ (Coalgebra.counit (R := R) ((S.liftSeq hsurj hker v).1 j))

include hker in
theorem π_algebraMap {v : ℕ} {r : R} (hr : r ∈ 𝔪p) :
    π (k := k) v (algebraMap R (H.G v).A r) = 0 :=
  (π_eq_zero_iff hker _ _).mpr (Ideal.mem_map_of_mem _ hr)

theorem counit_mem (v : ℕ) (j : Fin d) :
    Coalgebra.counit (R := R) ((S.liftSeq hsurj hker v).1 j) ∈ 𝔪p := by
  set y := (S.liftSeq hsurj hker v).1 j
  obtain ⟨N, hN⟩ := S.exists_pow_eq_zero v j
  have h1 : y ^ N ∈ (𝔪p).map (algebraMap R (H.G v).A) := by
    rw [← π_eq_zero_iff hker, map_pow, (S.liftSeq hsurj hker v).2 j, hN]
  have hle : (𝔪p).map (algebraMap R (H.G v).A) ≤
      (𝔪p).comap (Bialgebra.counitAlgHom R (H.G v).A) :=
    Ideal.map_le_iff_le_comap.mpr fun r hr => by
      rw [Ideal.mem_comap, Ideal.mem_comap, AlgHom.commutes, Algebra.algebraMap_self,
        RingHom.id_apply]
      exact hr
  have h2 := hle h1
  rw [Ideal.mem_comap, map_pow, Bialgebra.counitAlgHom_apply] at h2
  exact (IsLocalRing.maximalIdeal.isMaximal _).isPrime.mem_of_pow_mem N h2

theorem π_Y (v : ℕ) (j : Fin d) : π v (S.Y hsurj hker v j) = S.ρ v (X j) := by
  rw [Y, map_sub, π_algebraMap hker (S.counit_mem hsurj hker v j), sub_zero,
    (S.liftSeq hsurj hker v).2 j]

theorem tnf_Y (v : ℕ) : FGL.TNF 𝔪p (S.Y hsurj hker v) := fun j => by
  obtain ⟨N, hN⟩ := S.exists_pow_eq_zero v j
  refine ⟨N, ?_⟩
  rw [← π_eq_zero_iff hker, map_pow, π_Y, hN]

theorem counit_Y (v : ℕ) (j : Fin d) :
    Coalgebra.counit (R := R) (S.Y hsurj hker v j) = 0 :=
  counit_sub_algebraMap _

theorem incl_Y (v : ℕ) (j : Fin d) : H.incl v (S.Y hsurj hker (v + 1) j) = S.Y hsurj hker v j := by
  rw [Y, Y, map_sub, AlgHomClass.commutes, S.incl_liftSeq hsurj hker v j]
  congr 2
  rw [← S.incl_liftSeq hsurj hker v j]
  exact (CoalgHomClass.counit_comp_apply (H.incl v) _).symm

variable [IsAdicComplete (maximalIdeal R) R]

/-- `f_v : R[[t]] → A_v`. -/
def ev (v : ℕ) : MvPowerSeries (Fin d) R →ₐ[R] (H.G v).A :=
  evalT (S.Y hsurj hker v) (S.tnf_Y hsurj hker v)

omit [IsAdicComplete 𝔪p R] in
include hker in
theorem map_bot (v : ℕ) :
    (𝔪p).map (algebraMap R (k ⊗[R] (H.G v).A)) = ⊥ := by
  rw [eq_bot_iff, Ideal.map_le_iff_le_comap]
  intro r hr
  rw [Ideal.mem_comap, Ideal.mem_bot, Algebra.TensorProduct.algebraMap_apply, (hker r).mpr hr,
    TensorProduct.zero_tmul]

/-- The reduction `R[[t]] → k[[t]]` followed by `ρ̄_v`, an `R`-algebra map. -/
def redρ (v : ℕ) : MvPowerSeries (Fin d) R →ₐ[R] k ⊗[R] (H.G v).A :=
  { (S.ρ v).toRingHom.comp (MvPowerSeries.map (algebraMap R k)) with
    commutes' := fun r => by
      simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe,
        MonoidHom.coe_coe, RingHom.coe_comp, Function.comp_apply]
      rw [← C_eq_algebraMap, map_C]
      have e : (C (algebraMap R k r) : MvPowerSeries (Fin d) k) =
          algebraMap k _ (algebraMap R k r) := by
        rw [MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
      rw [e]
      exact ((S.ρ v).commutes _).trans (IsScalarTower.algebraMap_apply _ k _ r).symm }

omit [IsLocalRing R] in
theorem redρ_apply (v : ℕ) (g : MvPowerSeries (Fin d) R) :
    S.redρ v g = S.ρ v (MvPowerSeries.map (algebraMap R k) g) := rfl

/-- **`f_v` reduces to `ρ̄_v`.** -/
theorem π_ev (v : ℕ) (g : MvPowerSeries (Fin d) R) :
    π v (S.ev hsurj hker v g) = S.ρ v (MvPowerSeries.map (algebraMap R k) g) := by
  haveI : IsHausdorff ((𝔪p).map (algebraMap R (k ⊗[R] (H.G v).A)))
      (k ⊗[R] (H.G v).A) := by
    rw [map_bot (H := H) hker v]; infer_instance
  have key : (π v).comp (S.ev hsurj hker v) = S.redρ v := by
    refine algHom_ext_topNil (𝔪 := 𝔪p) (fun j => ?_) fun j => ?_
    · rw [AlgHom.comp_apply, ev, evalT_X, π_Y]
      obtain ⟨N, hN⟩ := S.exists_pow_eq_zero v j
      exact ⟨N, by rw [hN]; exact zero_mem _⟩
    · rw [AlgHom.comp_apply, ev, evalT_X, π_Y, redρ_apply, map_X]
  exact congrArg (fun φ => φ g) key

theorem ev_surjective (v : ℕ) : Function.Surjective (S.ev hsurj hker v) := by
  have key : (⊤ : Submodule R (H.G v).A) ≤
      LinearMap.range (S.ev hsurj hker v).toLinearMap ⊔ 𝔪p • ⊤ := by
    intro a _
    obtain ⟨gb, hgb⟩ := S.surj v (π v a)
    choose c hc using fun m => hsurj (coeff m gb)
    let g : MvPowerSeries (Fin d) R := fun m => c m
    have hg : MvPowerSeries.map (algebraMap R k) g = gb := by
      ext m
      rw [coeff_map]
      exact hc m
    have hmem : a - S.ev hsurj hker v g ∈ (𝔪p).map (algebraMap R (H.G v).A) := by
      rw [← π_eq_zero_iff hker, map_sub, S.π_ev hsurj hker, hg, hgb, sub_self]
    have h2 : a - S.ev hsurj hker v g ∈ 𝔪p • (⊤ : Submodule R (H.G v).A) := by
      rw [Ideal.smul_top_eq_map, Submodule.restrictScalars_mem]
      exact hmem
    have := Submodule.add_mem_sup (LinearMap.mem_range_self (S.ev hsurj hker v).toLinearMap g) h2
    rwa [AlgHom.toLinearMap_apply, add_sub_cancel] at this
  have htop := Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top
    (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge key
  intro a
  obtain ⟨g, hg⟩ := htop (Submodule.mem_top : a ∈ ⊤)
  exact ⟨g, hg⟩

/-- **`⋂_v ker f_v = 0`.** -/
theorem eq_zero [IsDomain R] [CoeffRing R] [Fact p.Prime] {g : MvPowerSeries (Fin d) R}
    (hg : ∀ v, S.ev hsurj hker v g = 0) :
    g = 0 :=
  eq_zero_of_forall_red (k := k) (fun r => (hker r).mp)
    (fun v _ _ hr h => eq_zero_of_smul_eq_zero hr h) (S.ev hsurj hker) (fun v => p ^ v)
    (fun n => ⟨n, (Nat.lt_pow_self (Fact.out : p.Prime).one_lt).le⟩)
    (fun v g hg => spanXPow_le_boxIdeal _ (S.ker_le v (by
      rw [RingHom.mem_ker, ← S.π_ev hsurj hker, hg, map_zero])))
    hg

/-- **Coordinates on `H` from the special fibre.** -/
def coords [IsDomain R] [CoeffRing R] [Fact p.Prime] : Coords H d where
  y := S.Y hsurj hker
  tnf := S.tnf_Y hsurj hker
  counit_y := S.counit_Y hsurj hker
  incl_y := S.incl_Y hsurj hker
  surj := S.ev_surjective hsurj hker
  inj _ := S.eq_zero hsurj hker

end SpecialFibreData

/-- **Serre–Tate, essential surjectivity** ([Hong, Thm. 2.2.16]), given the special-fibre
coordinates: a connected `p`-divisible group `H` over `R` is isomorphic to `F[p^∞]` for a
`p`-divisible formal group law `F`. -/
theorem exists_iso_of_specialFibre [IsAdicComplete (maximalIdeal R) R] [IsDomain R]
    [CoeffRing R] [Fact p.Prime] {H : PDivGroup R p}
    (hconn : ∀ v, (H.G v).IsConnected) {k : Type} [Field k] [Algebra R k]
    (hsurj : Function.Surjective (algebraMap R k))
    (hker : ∀ r : R, algebraMap R k r = 0 ↔ r ∈ maximalIdeal R) {d : ℕ}
    (S : SpecialFibreData H k d) :
    ∃ (P : PDivFGL R d p) (φ : PDivGroup.Hom H P.pdivGroup)
      (ψ : PDivGroup.Hom P.pdivGroup H),
      φ.comp ψ = PDivGroup.Hom.id _ ∧ ψ.comp φ = PDivGroup.Hom.id _ :=
  (S.coords hsurj hker).exists_iso hconn

end SerreTate

end PadicHodge
