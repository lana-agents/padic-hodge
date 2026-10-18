/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.FormalGroup.GmHeight
import PadicHodge.FormalGroup.LayerPDiv
import PadicHodge.GroupScheme.TateMu
import PadicHodge.GroupScheme.PDivisibleHom

/-!
# `Ĝ_m[p^∞] ≅ μ_{p^∞}`

Let `R` be a complete local ring with `p ∈ 𝔪_R`. For the `p`-divisible formal group law `Ĝ_m`
of height `1` (`gmPDiv`, `FormalGroup/GmHeight.lean`), the `p`-divisible group
`Ĝ_m[p^∞] = (Spec R[[t]]/((1 + t)^{p^v} − 1))_v` (`PDivFGL.pdivGroup`) is isomorphic to
`μ_{p^∞} = (Spec R[ℤ/p^v])_v` (`muPDiv`), as stated in [Hong, Ex. 2.2.4 / proof of Thm. 2.2.16]
(the formal group of `μ_{p^∞}` is `Ĝ_m`):

* `toMuAlg v : R[ℤ/p^v] → A_v`, `[k] ↦ (1 + t)^k`, and `ofMuAlg v : A_v → R[ℤ/p^v]`,
  `t ↦ [1] − 1` (evaluation of power series: `[1] − 1` is topologically nilpotent since
  `([1] − 1)^{p^v} ≡ [p^v] − 1 = 0` modulo `p`), mutually inverse (`toMuAlg_ofMuAlg`,
  `ofMuAlg_toMuAlg`);
* both are bialgebra maps (`FGL.gm_addE`: `x +_{Ĝ_m} y = x + y + xy`, so `Δ(1 + t) =
  (1 + t) ⊗ (1 + t)`) compatible with the transition maps: homomorphisms of `p`-divisible groups
  `gmToMu`, `muToGm` with `muToGm ∘ gmToMu = id`, `gmToMu ∘ muToGm = id`; hence
  `T_p(Ĝ_m[p^∞]) ≅ T_p μ_{p^∞}` (`tateEquiv`).
-/

noncomputable section

open MvPowerSeries IsLocalRing PadicHodge.AdicEval TensorProduct

namespace PadicHodge

universe u

namespace FGL

/-- **The group law of `Ĝ_m` on topologically nilpotent elements**: `x + y + xy`. -/
theorem gm_addE {R : Type*} [CommRing R] {𝔪 : Ideal R} {S : Type*} [CommRing S] [Algebra R S]
    [IsAdicComplete (𝔪.map (algebraMap R S)) S] {x y : Fin 1 → S} (hx : TNF 𝔪 x)
    (hy : TNF 𝔪 y) : (multiplicative R).addE 𝔪 x y 0 = x 0 + y 0 + x 0 * y 0 := by
  rw [addE, evF_of (tnf_pairS hx hy)]
  change evalT _ _ (multΦ R) = _
  simp only [multΦ, map_add, map_mul, evalT_X]
  rfl

end FGL

namespace GmMu

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsAdicComplete (maximalIdeal R) R]
  (p : ℕ) [hp : Fact p.Prime] (hpR : (p : R) ∈ maximalIdeal R)

attribute [local instance] PDivFGL.isAdicComplete_free

local notation "𝔪R" => maximalIdeal R

/-- `Ĝ_m` as a `p`-divisible formal group law. -/
abbrev G : PDivFGL R 1 p := gmPDiv R p hpR

/-- `1 + t ∈ A_v`. -/
abbrev u (v : ℕ) : (G p hpR).A v := 1 + (G p hpR).t v 0

theorem u_pow (v : ℕ) : u p hpR v ^ (p ^ v) = 1 := by
  have h := (G p hpR).mk_mulPS v 0
  change Ideal.Quotient.mk _ ((FGL.multiplicative R).mulPS (p ^ v) 0) = 0 at h
  rw [FGL.gm_mulPS, map_sub, map_pow, map_add, map_one, sub_eq_zero] at h
  exact h

theorem u_pow_val_one (v : ℕ) :
    u p hpR v ^ (Multiplicative.toAdd (genP p v)).val = u p hpR v := by
  rw [toAdd_ofAdd, ZMod.val_one_eq_one_mod, pow_mod_of_pow_eq_one (u_pow p hpR v), pow_one]

/-- The character `ℤ/p^v → A_v`, `k ↦ (1 + t)^k`. -/
def chi (v : ℕ) : CycP p v →* (G p hpR).A v where
  toFun a := u p hpR v ^ (Multiplicative.toAdd a).val
  map_one' := by simp
  map_mul' a b := by
    rw [toAdd_mul, ZMod.val_add, pow_mod_of_pow_eq_one (u_pow p hpR v), pow_add]

theorem chi_apply (v : ℕ) (a : CycP p v) :
    chi p hpR v a = u p hpR v ^ (Multiplicative.toAdd a).val := rfl

theorem chi_genP (v : ℕ) : chi p hpR v (genP p v) = u p hpR v := u_pow_val_one p hpR v

/-- `R[ℤ/p^v] → A_v`, `[k] ↦ (1 + t)^k`. -/
def toMuAlg (v : ℕ) : MonoidAlgebra R (CycP p v) →ₐ[R] (G p hpR).A v :=
  MonoidAlgebra.lift R ((G p hpR).A v) (CycP p v) (chi p hpR v)

theorem toMuAlg_single (v : ℕ) (a : CycP p v) :
    toMuAlg p hpR v (MonoidAlgebra.single a 1) = chi p hpR v a := by
  rw [toMuAlg, MonoidAlgebra.lift_single, one_smul]

/-! ### The inverse `A_v → R[ℤ/p^v]` -/

variable (R) in
/-- `[1] − 1 ∈ R[ℤ/p^v]`. -/
abbrev w (v : ℕ) : MonoidAlgebra R (CycP p v) := MonoidAlgebra.single (genP p v) 1 - 1

omit [IsLocalRing R] [IsAdicComplete (maximalIdeal R) R] hp in
theorem single_genP_pow (v : ℕ) :
    (MonoidAlgebra.single (genP p v) (1 : R)) ^ (p ^ v) = 1 := by
  rw [MonoidAlgebra.single_pow, genP_pow_card, one_pow, MonoidAlgebra.one_def]

omit [IsAdicComplete (maximalIdeal R) R] in
include hpR in
theorem topNil_w (v : ℕ) : TopNil 𝔪R (w R p v) := by
  refine ⟨p ^ v, ?_⟩
  set Q := MonoidAlgebra R (CycP p v) ⧸ (𝔪R).map (algebraMap R (MonoidAlgebra R (CycP p v)))
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  rcases subsingleton_or_nontrivial Q with hQ | hQ
  · exact Subsingleton.elim _ _
  haveI : CharP Q p := (CharP.charP_iff_prime_eq_zero hp.out).mpr (by
    rw [← map_natCast (Ideal.Quotient.mk _), Ideal.Quotient.eq_zero_iff_mem,
      ← map_natCast (algebraMap R _)]
    exact Ideal.mem_map_of_mem _ hpR)
  rw [map_pow, w, map_sub, map_one, sub_pow_char_pow, one_pow, ← map_pow, single_genP_pow,
    map_one, sub_self]

/-- `R[[t]] → R[ℤ/p^v]`, `t ↦ [1] − 1`. -/
def evW (v : ℕ) : MvPowerSeries (Fin 1) R →ₐ[R] MonoidAlgebra R (CycP p v) :=
  evalT (𝔪 := 𝔪R) (fun _ => w R p v) (fun _ => topNil_w p hpR v)

theorem evW_X (v : ℕ) : evW p hpR v (X 0) = w R p v := by
  rw [evW, evalT_X]

theorem evW_mulPS (v : ℕ) : evW p hpR v ((FGL.multiplicative R).mulPS (p ^ v) 0) = 0 := by
  rw [FGL.gm_mulPS, map_sub, map_pow, map_add, map_one, evW_X, w, add_sub_cancel,
    single_genP_pow, sub_self]

/-- `A_v → R[ℤ/p^v]`, `t ↦ [1] − 1`. -/
def ofMuAlg (v : ℕ) : (G p hpR).A v →ₐ[R] MonoidAlgebra R (CycP p v) :=
  (G p hpR).liftL v (evW p hpR v) fun j => by
    rw [Subsingleton.elim j 0]
    exact evW_mulPS p hpR v

theorem ofMuAlg_t (v : ℕ) : ofMuAlg p hpR v ((G p hpR).t v 0) = w R p v := by
  rw [ofMuAlg, PDivFGL.liftL_t, evW_X]

theorem ofMuAlg_u (v : ℕ) :
    ofMuAlg p hpR v (u p hpR v) = MonoidAlgebra.single (genP p v) 1 := by
  rw [u, map_add, map_one, ofMuAlg_t, w, add_sub_cancel]

theorem ofMuAlg_toMuAlg (v : ℕ) :
    (ofMuAlg p hpR v).comp (toMuAlg p hpR v) = AlgHom.id R _ := by
  refine MonoidAlgebra.algHom_ext (fun a => ?_) (Subsingleton.elim _ _)
  rw [AlgHom.comp_apply, toMuAlg_single, chi_apply, map_pow, ofMuAlg_u, AlgHom.id_apply,
    MonoidAlgebra.single_pow, one_pow, ← eq_genP_pow]

theorem toMuAlg_ofMuAlg (v : ℕ) :
    (toMuAlg p hpR v).comp (ofMuAlg p hpR v) = AlgHom.id R _ := by
  refine (G p hpR).algHom_ext_A v fun j => ?_
  rw [Subsingleton.elim j 0, AlgHom.comp_apply, ofMuAlg_t, w, map_sub, map_one, toMuAlg_single,
    chi_genP, AlgHom.id_apply, u, add_sub_cancel_left]

/-! ### Bialgebra maps -/

theorem comul_t (v : ℕ) :
    (G p hpR).comul v ((G p hpR).t v 0) =
      (G p hpR).t v 0 ⊗ₜ 1 + 1 ⊗ₜ (G p hpR).t v 0 + (G p hpR).t v 0 ⊗ₜ (G p hpR).t v 0 := by
  have h : (G p hpR).wΔ v 0 = _ :=
    FGL.gm_addE (R := R) (𝔪 := 𝔪R) ((G p hpR).tnf_tL v) ((G p hpR).tnf_tR v)
  rw [PDivFGL.comul_t, h]
  simp only [PDivFGL.tL, PDivFGL.tR, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]

theorem counit_u (v : ℕ) : (G p hpR).counit v (u p hpR v) = 1 := by
  rw [u, map_add, map_one, PDivFGL.counit_t, add_zero]

theorem comul_u (v : ℕ) : (G p hpR).comul v (u p hpR v) = u p hpR v ⊗ₜ u p hpR v := by
  rw [u, map_add, map_one, comul_t]
  simp only [add_tmul, tmul_add, Algebra.TensorProduct.one_def]
  abel

omit [IsLocalRing R] [IsAdicComplete 𝔪R R] hp in
theorem comul_single (v : ℕ) (a : CycP p v) :
    Coalgebra.comul (R := R) (MonoidAlgebra.single a (1 : R)) =
      MonoidAlgebra.single a 1 ⊗ₜ MonoidAlgebra.single a 1 := by
  rw [MonoidAlgebra.comul_single]; simp

/-- **`Ĝ_m[p^v] → μ_{p^v}`**: the bialgebra map `[k] ↦ (1 + t)^k`. -/
def toMu (v : ℕ) : FFGroupScheme.Hom ((G p hpR).groupScheme v) (muP R p v) :=
  letI := (G p hpR).hopfAlgebra v
  BialgHom.ofAlgHom (A := MonoidAlgebra R (CycP p v)) (B := (G p hpR).A v) (toMuAlg p hpR v)
    (by
      refine MonoidAlgebra.algHom_ext (fun a => ?_) (Subsingleton.elim _ _)
      change (G p hpR).counit v (toMuAlg p hpR v (MonoidAlgebra.single a 1)) =
        Coalgebra.counit (R := R) (MonoidAlgebra.single a (1 : R))
      rw [MonoidAlgebra.counit_single, toMuAlg_single, chi_apply, map_pow, counit_u, one_pow]
      rfl)
    (by
      refine MonoidAlgebra.algHom_ext (fun a => ?_) (Subsingleton.elim _ _)
      change Algebra.TensorProduct.map (toMuAlg p hpR v) (toMuAlg p hpR v)
          (Coalgebra.comul (R := R) (MonoidAlgebra.single a (1 : R))) =
        (G p hpR).comul v (toMuAlg p hpR v (MonoidAlgebra.single a 1))
      rw [comul_single, Algebra.TensorProduct.map_tmul, toMuAlg_single, chi_apply, map_pow,
        comul_u, Algebra.TensorProduct.tmul_pow])

theorem toMu_apply (v : ℕ) (x : MonoidAlgebra R (CycP p v)) :
    toMu p hpR v x = toMuAlg p hpR v x := rfl

/-- **`μ_{p^v} → Ĝ_m[p^v]`**: the bialgebra map `t ↦ [1] − 1`. -/
def ofMu (v : ℕ) : FFGroupScheme.Hom (muP R p v) ((G p hpR).groupScheme v) :=
  letI := (G p hpR).hopfAlgebra v
  BialgHom.ofAlgHom (B := MonoidAlgebra R (CycP p v)) (A := (G p hpR).A v) (ofMuAlg p hpR v)
    (by
      refine (G p hpR).algHom_ext_A v fun j => ?_
      rw [Subsingleton.elim j 0]
      change Coalgebra.counit (R := R) (ofMuAlg p hpR v ((G p hpR).t v 0)) =
        (G p hpR).counit v ((G p hpR).t v 0)
      rw [ofMuAlg_t, PDivFGL.counit_t, w, map_sub, MonoidAlgebra.counit_single]
      simp only [Bialgebra.counit_one, sub_self])
    (by
      refine (G p hpR).algHom_ext_A v fun j => ?_
      rw [Subsingleton.elim j 0]
      change Algebra.TensorProduct.map (ofMuAlg p hpR v) (ofMuAlg p hpR v)
          ((G p hpR).comul v ((G p hpR).t v 0)) =
        Coalgebra.comul (R := R) (ofMuAlg p hpR v ((G p hpR).t v 0))
      rw [comul_t, ofMuAlg_t, w, map_sub, comul_single, Bialgebra.comul_one]
      simp only [map_add, Algebra.TensorProduct.map_tmul, ofMuAlg_t, map_one, w,
        sub_tmul, tmul_sub, Algebra.TensorProduct.one_def]
      abel)

theorem ofMu_apply (v : ℕ) (x : (G p hpR).A v) : ofMu p hpR v x = ofMuAlg p hpR v x := rfl

/-! ### `Ĝ_m[p^∞] ≅ μ_{p^∞}` -/

theorem layerIncl_u (v : ℕ) : (G p hpR).F.layerIncl p v (u p hpR (v + 1)) = u p hpR v := by
  rw [u, u, map_add, map_one, PDivFGL.layerIncl_t]

theorem layerIncl_chi (v : ℕ) (a : CycP p (v + 1)) :
    (G p hpR).F.layerIncl p v (chi p hpR (v + 1) a) = chi p hpR v (redP p v a) := by
  obtain ⟨k, rfl⟩ : ∃ k, a = genP p (v + 1) ^ k := ⟨_, eq_genP_pow p a⟩
  simp only [map_pow, chi_genP, layerIncl_u, redP_genP]

/-- **The homomorphism `Ĝ_m[p^∞] → μ_{p^∞}`.** -/
def gmToMu : PDivGroup.Hom (G p hpR).pdivGroup (muPDiv R p) where
  f := toMu p hpR
  comm v := by
    apply BialgHom.coe_toAlgHom_injective
    refine MonoidAlgebra.algHom_ext (fun a => ?_) (Subsingleton.elim _ _)
    change (G p hpR).F.layerIncl p v (toMuAlg p hpR (v + 1) (MonoidAlgebra.single a 1)) =
      toMuAlg p hpR v (MonoidAlgebra.mapDomain (redP p v) (MonoidAlgebra.single a 1))
    rw [toMuAlg_single, layerIncl_chi, MonoidAlgebra.mapDomain_single, toMuAlg_single]

/-- **The homomorphism `μ_{p^∞} → Ĝ_m[p^∞]`.** -/
def muToGm : PDivGroup.Hom (muPDiv R p) (G p hpR).pdivGroup where
  f := ofMu p hpR
  comm v := by
    apply BialgHom.coe_toAlgHom_injective
    refine (G p hpR).algHom_ext_A (v + 1) fun j => ?_
    rw [Subsingleton.elim j 0]
    change (MonoidAlgebra.mapDomainBialgHom R (redP p v))
        (ofMuAlg p hpR (v + 1) ((G p hpR).t (v + 1) 0)) =
      ofMuAlg p hpR v ((G p hpR).F.layerIncl p v ((G p hpR).t (v + 1) 0))
    rw [PDivFGL.layerIncl_t, ofMuAlg_t, ofMuAlg_t, w, w, map_sub, map_one]
    congr 1
    change MonoidAlgebra.mapDomain (redP p v) (MonoidAlgebra.single _ 1) = _
    rw [MonoidAlgebra.mapDomain_single, redP_genP]

omit [IsLocalRing R] [IsAdicComplete 𝔪R R] hp in
theorem hom_ext {H K : PDivGroup R p} {φ ψ : PDivGroup.Hom H K} (h : ∀ v, φ.f v = ψ.f v) :
    φ = ψ := by
  cases φ; cases ψ; congr; funext v; exact h v

/-- `μ_{p^∞} → Ĝ_m[p^∞] → μ_{p^∞}` is the identity. -/
theorem gmToMu_comp_muToGm :
    (gmToMu p hpR).comp (muToGm p hpR) = PDivGroup.Hom.id (muPDiv R p) :=
  hom_ext p fun v => BialgHom.ext fun x => DFunLike.congr_fun (ofMuAlg_toMuAlg p hpR v) x

/-- `Ĝ_m[p^∞] → μ_{p^∞} → Ĝ_m[p^∞]` is the identity. -/
theorem muToGm_comp_gmToMu :
    (muToGm p hpR).comp (gmToMu p hpR) = PDivGroup.Hom.id (G p hpR).pdivGroup :=
  hom_ext p fun v => BialgHom.ext fun x => DFunLike.congr_fun (toMuAlg_ofMuAlg p hpR v) x

/-- **`T_p(Ĝ_m[p^∞]) ≅ T_p μ_{p^∞}`** on `S`-points. -/
def tateEquiv (S : Type u) [CommRing S] [Algebra R S] :
    (G p hpR).pdivGroup.TateModule S ≃* (muPDiv R p).TateModule S where
  toFun := (gmToMu p hpR).mapTate S
  invFun := (muToGm p hpR).mapTate S
  left_inv x := by
    rw [← PDivGroup.Hom.mapTate_comp, muToGm_comp_gmToMu, PDivGroup.Hom.mapTate_id]
  right_inv x := by
    rw [← PDivGroup.Hom.mapTate_comp, gmToMu_comp_muToGm, PDivGroup.Hom.mapTate_id]
  map_mul' := map_mul _

end GmMu

end PadicHodge
