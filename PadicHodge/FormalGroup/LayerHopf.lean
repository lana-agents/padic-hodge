/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.FormalGroup.AdicPoints
import PadicHodge.FormalGroup.LayerFree
import PadicHodge.GroupScheme.FiniteFlat
import Mathlib.RingTheory.LocalRing.Quotient
import Mathlib.RingTheory.MvPowerSeries.Inverse

/-!
# The finite flat group schemes `F[p^v] = Spec A_v` ([Hong, Prop. 2.2.10 (1)])

Let `R` be a complete local ring (`IsAdicComplete (maximalIdeal R) R`, e.g. `ℤ_p`) and `F` a
`p`-divisible formal group law of height `h` over `R` (`PDivFGL`). The layer
`A_v = R[[T]]/[p^v]_F(I)` is finite free of rank `p^{hv}` (`FormalGroup/LayerFree.lean`), and:

* the images `t_j` of the variables are topologically nilpotent in `A_v` (`tnf_t`):
  `A_v/𝔪A_v` is artinian local, so its maximal ideal is nilpotent;
* hence power series can be evaluated in `A_v`, `A_v ⊗ A_v`, … (`FormalGroup/AdicEval.lean`), and
  `R`-algebra maps out of `A_v` into finite free `R`-algebras are determined by the images of the
  `t_j` (`algHom_ext_A`);
* **comultiplication** `t ↦ Φ(t ⊗ 1, 1 ⊗ t)` (`comul`), **counit** `t ↦ 0` (`counit`) and
  **antipode** `t ↦ [p^v − 1]_F(t)` (`antipode`; since `[p^v]_F(t) = 0` in `A_v`, this is the
  inverse, and the formal inverse `ι(T)` of [Hong, Lemma 2.2.5 (3)] is not needed);
* the Hopf axioms and cocommutativity follow from the axioms of `F`
  (`FormalGroup/AdicPoints.lean`): `F[p^v]` is a finite flat commutative group scheme of order
  `p^{hv}` (`groupScheme`, `order_groupScheme`).
-/

noncomputable section

open MvPowerSeries IsLocalRing PadicHodge.AdicEval TensorProduct

namespace PadicHodge

universe u

/-- A `p`-divisible formal group law of height `height` ([Hong, Def. 2.2.9]). -/
structure PDivFGL (R : Type u) [CommRing R] (d p : ℕ) where
  /-- the formal group law -/
  F : FGL R d
  /-- the height -/
  height : ℕ
  isPDivisible : F.IsPDivisible p height

namespace PDivFGL

section Basic

variable {R : Type u} [CommRing R] {d p : ℕ} (P : PDivFGL R d p)

/-- The layer `A_v = R[[T]]/[p^v]_F(I)`. -/
abbrev A (v : ℕ) : Type u := P.F.Layer p v

instance instFree (v : ℕ) : Module.Free R (P.A v) := FGL.layer_free P.isPDivisible v

instance instFinite (v : ℕ) : Module.Finite R (P.A v) := FGL.layer_finite P.isPDivisible v

/-- The coordinates `t_j ∈ A_v`. -/
def t (v : ℕ) : Fin d → P.A v := fun j => Ideal.Quotient.mk (P.F.layerIdeal p v) (X j)

theorem mk_mulPS (v : ℕ) (j : Fin d) :
    Ideal.Quotient.mk (P.F.layerIdeal p v) (P.F.mulPS (p ^ v) j) = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (P.F.mulPS_mem_layerIdeal p v j)

/-- Descend an algebra map `R[[T]] → S` killing `[p^v]_F(t_j)` to `A_v`. -/
def liftL (v : ℕ) {S : Type*} [CommRing S] [Algebra R S]
    (φ : MvPowerSeries (Fin d) R →ₐ[R] S) (hφ : ∀ j, φ (P.F.mulPS (p ^ v) j) = 0) :
    P.A v →ₐ[R] S :=
  Ideal.Quotient.liftₐ _ φ fun a ha => by
    have : P.F.layerIdeal p v ≤ RingHom.ker φ := by
      rw [FGL.layerIdeal, Ideal.span_le]
      rintro _ ⟨j, rfl⟩
      exact hφ j
    exact this ha

theorem liftL_mk (v : ℕ) {S : Type*} [CommRing S] [Algebra R S]
    (φ : MvPowerSeries (Fin d) R →ₐ[R] S) (hφ : ∀ j, φ (P.F.mulPS (p ^ v) j) = 0)
    (f : MvPowerSeries (Fin d) R) :
    P.liftL v φ hφ (Ideal.Quotient.mk _ f) = φ f := by
  rw [liftL, Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk]
  rfl

theorem liftL_t (v : ℕ) {S : Type*} [CommRing S] [Algebra R S]
    (φ : MvPowerSeries (Fin d) R →ₐ[R] S) (hφ : ∀ j, φ (P.F.mulPS (p ^ v) j) = 0) (j : Fin d) :
    P.liftL v φ hφ (P.t v j) = φ (X j) :=
  P.liftL_mk v φ hφ (X j)

end Basic

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsAdicComplete (maximalIdeal R) R]
  {d p : ℕ} [hp : Fact p.Prime] (P : PDivFGL R d p)

theorem isAdicComplete_free (S : Type*) [CommRing S]
    [Algebra R S] [Module.Free R S] [Module.Finite R S] :
    IsAdicComplete ((maximalIdeal R).map (algebraMap R S)) S :=
  isAdicComplete_of_free _ S

attribute [local instance] isAdicComplete_free

local notation "𝔪R" => maximalIdeal R

omit [IsAdicComplete (maximalIdeal R) R] [IsLocalRing R] in
theorem nontrivial_A [Nontrivial R] (v : ℕ) : Nontrivial (P.A v) :=
  Module.nontrivial_of_finrank_pos (R := R) (by
    rw [FGL.finrank_layer P.isPDivisible v]
    exact pow_pos hp.out.pos _)

omit [IsAdicComplete (maximalIdeal R) R] in
/-- **The coordinates of `A_v` are topologically nilpotent**: `A_v/𝔪A_v` is artinian local. -/
theorem tnf_t (v : ℕ) : FGL.TNF 𝔪R (P.t v) := by
  intro j
  haveI := P.nontrivial_A v
  haveI : IsLocalRing (P.A v) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  letI := Ideal.Quotient.field (maximalIdeal R)
  haveI : IsArtinianRing (P.A v ⧸ (maximalIdeal R).map (algebraMap R (P.A v))) := by
    haveI : Module.Finite (R ⧸ maximalIdeal R)
        (P.A v ⧸ (maximalIdeal R).map (algebraMap R (P.A v))) :=
      Module.Finite.of_restrictScalars_finite R _ _
    exact IsArtinianRing.of_finite (R ⧸ maximalIdeal R) _
  obtain ⟨n, hn⟩ := IsLocalRing.exists_maximalIdeal_pow_le_of_isArtinianRing_quotient
    ((maximalIdeal R).map (algebraMap R (P.A v)))
  refine ⟨n, hn (Ideal.pow_mem_pow ?_ n)⟩
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  haveI : IsLocalHom (Ideal.Quotient.mk (P.F.layerIdeal p v)) :=
    IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  have := (isUnit_map_iff (Ideal.Quotient.mk (P.F.layerIdeal p v)) (X j)).mp hu
  rw [MvPowerSeries.isUnit_iff_constantCoeff, constantCoeff_X] at this
  exact not_isUnit_zero this

/-- **Maps out of `A_v` into finite free `R`-algebras are determined on the `t_j`.** -/
theorem algHom_ext_A (v : ℕ) {S : Type*} [CommRing S] [Algebra R S] [Module.Free R S]
    [Module.Finite R S] {φ ψ : P.A v →ₐ[R] S} (h : ∀ j, φ (P.t v j) = ψ (P.t v j)) :
    φ = ψ := by
  apply Ideal.Quotient.algHom_ext R
  exact algHom_ext_topNil (𝔪 := 𝔪R) (fun j => (P.tnf_t v j).map φ) h

theorem evF_t (v : ℕ) (f : MvPowerSeries (Fin d) R) :
    FGL.evF 𝔪R (P.t v) f = Ideal.Quotient.mk _ f := by
  rw [FGL.evF_of (P.tnf_t v)]
  have := algHom_ext_topNil (𝔪 := 𝔪R) (φ := evalT (P.t v) (P.tnf_t v))
    (ψ := Ideal.Quotient.mkₐ R (P.F.layerIdeal p v))
    (fun j => by rw [evalT_X]; exact P.tnf_t v j) (fun j => by rw [evalT_X]; rfl)
  rw [this]
  rfl

theorem mulE_t (v : ℕ) : P.F.mulE 𝔪R (p ^ v) (P.t v) = 0 := by
  funext j
  rw [FGL.mulE, evF_t, mk_mulPS]
  rfl

theorem mulE_map_t (v : ℕ) {S : Type*} [CommRing S] [Algebra R S] [Module.Free R S]
    [Module.Finite R S] (g : P.A v →ₐ[R] S) :
    P.F.mulE 𝔪R (p ^ v) (fun k => g (P.t v k)) = 0 := by
  funext k
  rw [← FGL.mulE_comp P.F g _ (P.tnf_t v), mulE_t]
  simp

omit hp in
/-- An algebra map applied to `Φ(x, y)`. -/
theorem addE_map {S S' : Type*} [CommRing S] [Algebra R S] [Module.Free R S] [Module.Finite R S]
    [CommRing S'] [Algebra R S'] [Module.Free R S'] [Module.Finite R S'] (g : S →ₐ[R] S')
    {x y : Fin d → S} (hx : FGL.TNF 𝔪R x) (hy : FGL.TNF 𝔪R y) {x' y' : Fin d → S'}
    (hx' : ∀ k, g (x k) = x' k) (hy' : ∀ k, g (y k) = y' k) (j : Fin d) :
    g (P.F.addE 𝔪R x y j) = P.F.addE 𝔪R x' y' j := by
  rw [FGL.addE_comp P.F g hx hy, funext hx', funext hy']

/-! ### Comultiplication, counit, antipode -/

/-- `t ⊗ 1`. -/
def tL (v : ℕ) : Fin d → P.A v ⊗[R] P.A v := fun j => P.t v j ⊗ₜ 1

/-- `1 ⊗ t`. -/
def tR (v : ℕ) : Fin d → P.A v ⊗[R] P.A v := fun j => 1 ⊗ₜ P.t v j

omit [IsAdicComplete (maximalIdeal R) R] in
theorem tnf_tL (v : ℕ) : FGL.TNF 𝔪R (P.tL v) := fun j => by
  simpa [tL] using (P.tnf_t v j).map (Algebra.TensorProduct.includeLeft (S := R) (R := R)
    (A := P.A v) (B := P.A v))

omit [IsAdicComplete (maximalIdeal R) R] in
theorem tnf_tR (v : ℕ) : FGL.TNF 𝔪R (P.tR v) := fun j => by
  simpa [tR] using (P.tnf_t v j).map (Algebra.TensorProduct.includeRight (R := R)
    (A := P.A v) (B := P.A v))

/-- `Φ(t ⊗ 1, 1 ⊗ t)`. -/
def wΔ (v : ℕ) : Fin d → P.A v ⊗[R] P.A v := P.F.addE 𝔪R (P.tL v) (P.tR v)

theorem tnf_wΔ (v : ℕ) : FGL.TNF 𝔪R (P.wΔ v) := P.F.tnf_addE (P.tnf_tL v) (P.tnf_tR v)

theorem mulE_tL (v : ℕ) : P.F.mulE 𝔪R (p ^ v) (P.tL v) = 0 := by
  have := P.mulE_map_t v (Algebra.TensorProduct.includeLeft (S := R) (R := R) (A := P.A v)
    (B := P.A v))
  simp only [Algebra.TensorProduct.includeLeft_apply] at this
  exact this

theorem mulE_tR (v : ℕ) : P.F.mulE 𝔪R (p ^ v) (P.tR v) = 0 := by
  have := P.mulE_map_t v (Algebra.TensorProduct.includeRight (R := R) (A := P.A v)
    (B := P.A v))
  simp only [Algebra.TensorProduct.includeRight_apply] at this
  exact this

/-- **The comultiplication** `t ↦ Φ(t ⊗ 1, 1 ⊗ t)` of `A_v`. -/
def comul (v : ℕ) : P.A v →ₐ[R] P.A v ⊗[R] P.A v :=
  P.liftL v (evalT (P.wΔ v) (P.tnf_wΔ v)) fun j => by
    rw [← FGL.evF_of (P.tnf_wΔ v)]
    change P.F.mulE 𝔪R (p ^ v) (P.wΔ v) j = 0
    rw [wΔ, FGL.mulE_addE _ _ (P.tnf_tL v) (P.tnf_tR v), mulE_tL, mulE_tR,
      FGL.addE_zero _ FGL.tnf_zero]
    rfl

theorem comul_t (v : ℕ) (j : Fin d) : P.comul v (P.t v j) = P.wΔ v j := by
  rw [comul, liftL_t, evalT_X]

/-- **The counit** `t ↦ 0`. -/
def counit (v : ℕ) : P.A v →ₐ[R] R :=
  P.liftL v (FGL.constAlgHom (Fin d)) fun j => P.F.constantCoeff_mulPS _ j

omit [IsLocalRing R] [IsAdicComplete (maximalIdeal R) R] hp in
theorem counit_t (v : ℕ) (j : Fin d) : P.counit v (P.t v j) = 0 := by
  rw [counit, liftL_t]
  exact constantCoeff_X j

theorem tnf_neg (v : ℕ) : FGL.TNF 𝔪R (P.F.mulE 𝔪R (p ^ v - 1) (P.t v)) :=
  P.F.tnf_mulE _ (P.tnf_t v)

/-- **The antipode** `t ↦ [p^v − 1]_F(t)`. -/
def antipode (v : ℕ) : P.A v →ₐ[R] P.A v :=
  P.liftL v (evalT _ (P.tnf_neg v)) fun j => by
    rw [← FGL.evF_of (P.tnf_neg v)]
    change P.F.mulE 𝔪R (p ^ v) (P.F.mulE 𝔪R (p ^ v - 1) (P.t v)) j = 0
    rw [FGL.mulE_mulE _ _ _ (P.tnf_t v), mul_comm, ← FGL.mulE_mulE _ _ _ (P.tnf_t v), mulE_t,
      FGL.mulE_zero_fam]
    rfl

theorem antipode_t (v : ℕ) (j : Fin d) :
    P.antipode v (P.t v j) = P.F.mulE 𝔪R (p ^ v - 1) (P.t v) j := by
  rw [antipode, liftL_t, evalT_X]

/-- `x +_F [p^v − 1] x = 0` on `t`. -/
theorem addE_neg (v : ℕ) :
    P.F.addE 𝔪R (P.F.mulE 𝔪R (p ^ v - 1) (P.t v)) (P.t v) = 0 := by
  rw [← FGL.mulE_succ _ _ (P.tnf_t v), Nat.sub_add_cancel (Nat.one_le_pow _ _ hp.out.pos),
    mulE_t]

/-! ### The axioms -/

theorem coassoc (v : ℕ) :
    (Algebra.TensorProduct.assoc R R R (P.A v) (P.A v) (P.A v)).toAlgHom.comp
      ((Algebra.TensorProduct.map (P.comul v) (.id R (P.A v))).comp (P.comul v)) =
    (Algebra.TensorProduct.map (.id R (P.A v)) (P.comul v)).comp (P.comul v) := by
  set x : Fin d → P.A v ⊗[R] (P.A v ⊗[R] P.A v) := fun k => P.t v k ⊗ₜ (1 ⊗ₜ 1)
  set y : Fin d → P.A v ⊗[R] (P.A v ⊗[R] P.A v) := fun k => 1 ⊗ₜ (P.t v k ⊗ₜ 1)
  set z : Fin d → P.A v ⊗[R] (P.A v ⊗[R] P.A v) := fun k => 1 ⊗ₜ (1 ⊗ₜ P.t v k)
  have hx : FGL.TNF 𝔪R x := fun k => by
    have := (P.tnf_t v k).map (Algebra.TensorProduct.includeLeft (S := R) (R := R) (A := P.A v)
      (B := P.A v ⊗[R] P.A v))
    rwa [Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.one_def] at this
  have hy : FGL.TNF 𝔪R y := fun k => by
    have := (P.tnf_t v k).map ((Algebra.TensorProduct.includeRight (R := R) (A := P.A v)
      (B := P.A v ⊗[R] P.A v)).comp (Algebra.TensorProduct.includeLeft (S := R) (R := R)
      (A := P.A v) (B := P.A v)))
    rwa [AlgHom.comp_apply, Algebra.TensorProduct.includeLeft_apply,
      Algebra.TensorProduct.includeRight_apply] at this
  have hz : FGL.TNF 𝔪R z := fun k => by
    have := (P.tnf_t v k).map ((Algebra.TensorProduct.includeRight (R := R) (A := P.A v)
      (B := P.A v ⊗[R] P.A v)).comp (Algebra.TensorProduct.includeRight (R := R)
      (A := P.A v) (B := P.A v)))
    rwa [AlgHom.comp_apply, Algebra.TensorProduct.includeRight_apply,
      Algebra.TensorProduct.includeRight_apply] at this
  refine P.algHom_ext_A v fun j => ?_
  simp only [AlgHom.comp_apply, comul_t]
  -- left side
  have hL : ∀ k, (Algebra.TensorProduct.assoc R R R (P.A v) (P.A v) (P.A v))
      (Algebra.TensorProduct.map (P.comul v) (.id R (P.A v)) (P.tL v k)) =
      P.F.addE 𝔪R x y k := by
    intro k
    have e : Algebra.TensorProduct.map (P.comul v) (.id R (P.A v)) (P.tL v k) =
        Algebra.TensorProduct.includeLeft (S := R) (P.wΔ v k) := by
      simp [tL, comul_t]
    rw [e]
    exact P.addE_map ((Algebra.TensorProduct.assoc R R R (P.A v) (P.A v) (P.A v)).toAlgHom.comp
      (Algebra.TensorProduct.includeLeft (S := R))) (P.tnf_tL v) (P.tnf_tR v)
      (fun m => by simp [tL, x]) (fun m => by simp [tR, y]) k
  have hR : ∀ k, (Algebra.TensorProduct.assoc R R R (P.A v) (P.A v) (P.A v))
      (Algebra.TensorProduct.map (P.comul v) (.id R (P.A v)) (P.tR v k)) = z k := by
    intro k
    simp [tR, z, Algebra.TensorProduct.one_def]
  have h1 := P.addE_map ((Algebra.TensorProduct.assoc R R R (P.A v) (P.A v) (P.A v)).toAlgHom.comp
    (Algebra.TensorProduct.map (P.comul v) (.id R (P.A v)))) (P.tnf_tL v) (P.tnf_tR v)
    (x' := P.F.addE 𝔪R x y) (y' := z) hL hR j
  -- right side
  have hL' : ∀ k, Algebra.TensorProduct.map (.id R (P.A v)) (P.comul v) (P.tL v k) = x k := by
    intro k
    simp [tL, x, Algebra.TensorProduct.one_def]
  have hR' : ∀ k, Algebra.TensorProduct.map (.id R (P.A v)) (P.comul v) (P.tR v k) =
      P.F.addE 𝔪R y z k := by
    intro k
    have e : Algebra.TensorProduct.map (.id R (P.A v)) (P.comul v) (P.tR v k) =
        Algebra.TensorProduct.includeRight (P.wΔ v k) := by
      simp [tR, comul_t]
    rw [e]
    exact P.addE_map (Algebra.TensorProduct.includeRight) (P.tnf_tL v) (P.tnf_tR v)
      (x' := y) (y' := z) (fun m => by simp [tL, y]) (fun m => by simp [tR, z]) k
  have h2 := P.addE_map (Algebra.TensorProduct.map (.id R (P.A v)) (P.comul v)) (P.tnf_tL v)
    (P.tnf_tR v) hL' hR' j
  simp only [AlgHom.comp_apply] at h1
  rw [wΔ, h1, h2, FGL.addE_assoc _ hx hy hz]

theorem rTensor_counit (v : ℕ) :
    (Algebra.TensorProduct.map (P.counit v) (.id R (P.A v))).comp (P.comul v) =
      (Algebra.TensorProduct.lid R (P.A v)).symm := by
  refine P.algHom_ext_A v fun j => ?_
  rw [AlgHom.comp_apply, comul_t, wΔ]
  rw [P.addE_map _ (P.tnf_tL v) (P.tnf_tR v) (x' := 0)
    (y' := fun k => (Algebra.TensorProduct.lid R (P.A v)).symm (P.t v k))
    (fun k => by simp [tL, counit_t]) (fun k => by simp [tR]) j]
  have hT : FGL.TNF 𝔪R fun k => (Algebra.TensorProduct.lid R (P.A v)).symm (P.t v k) :=
    fun k => (P.tnf_t v k).map (Algebra.TensorProduct.lid R (P.A v)).symm.toAlgHom
  rw [FGL.zero_addE _ hT]
  rfl

theorem lTensor_counit (v : ℕ) :
    (Algebra.TensorProduct.map (.id R (P.A v)) (P.counit v)).comp (P.comul v) =
      (Algebra.TensorProduct.rid R R (P.A v)).symm := by
  refine P.algHom_ext_A v fun j => ?_
  rw [AlgHom.comp_apply, comul_t, wΔ]
  rw [P.addE_map _ (P.tnf_tL v) (P.tnf_tR v)
    (x' := fun k => (Algebra.TensorProduct.rid R R (P.A v)).symm (P.t v k)) (y' := 0)
    (fun k => by simp [tL]) (fun k => by simp [tR, counit_t]) j]
  have hT : FGL.TNF 𝔪R fun k => (Algebra.TensorProduct.rid R R (P.A v)).symm (P.t v k) :=
    fun k => (P.tnf_t v k).map (Algebra.TensorProduct.rid R R (P.A v)).symm.toAlgHom
  rw [FGL.addE_zero _ hT]
  rfl

theorem comm_comul (v : ℕ) :
    (Algebra.TensorProduct.comm R (P.A v) (P.A v)).toAlgHom.comp (P.comul v) = P.comul v := by
  refine P.algHom_ext_A v fun j => ?_
  simp only [AlgHom.comp_apply, comul_t]
  rw [wΔ]
  have := P.addE_map (Algebra.TensorProduct.comm R (P.A v) (P.A v)).toAlgHom (P.tnf_tL v)
    (P.tnf_tR v) (x' := P.tR v) (y' := P.tL v) (fun k => by simp [tL, tR])
    (fun k => by simp [tL, tR]) j
  rw [this, FGL.addE_comm _ (P.tnf_tR v) (P.tnf_tL v)]

/-- The bialgebra structure on `A_v`. -/
abbrev bialgebra (v : ℕ) : Bialgebra R (P.A v) :=
  Bialgebra.ofAlgHom (P.comul v) (P.counit v) (P.coassoc v) (P.rTensor_counit v)
    (P.lTensor_counit v)

theorem antipode_left (v : ℕ) :
    letI := P.bialgebra v
    (Algebra.TensorProduct.lift (P.antipode v) (.id R (P.A v)) fun _ _ ↦ Commute.all _ _).comp
      (Bialgebra.comulAlgHom R (P.A v)) =
      (Algebra.ofId R (P.A v)).comp (Bialgebra.counitAlgHom R (P.A v)) := by
  letI := P.bialgebra v
  refine P.algHom_ext_A v fun j => ?_
  change (Algebra.TensorProduct.lift (P.antipode v) (.id R (P.A v))
    fun _ _ ↦ Commute.all _ _) (P.comul v (P.t v j)) =
    algebraMap R (P.A v) (P.counit v (P.t v j))
  rw [comul_t, counit_t, map_zero, wΔ,
    P.addE_map _ (P.tnf_tL v) (P.tnf_tR v) (x' := P.F.mulE 𝔪R (p ^ v - 1) (P.t v))
      (y' := P.t v) (fun k => by simp [tL, antipode_t]) (fun k => by simp [tR]) j,
    addE_neg]
  rfl

theorem antipode_right (v : ℕ) :
    letI := P.bialgebra v
    (Algebra.TensorProduct.lift (.id R (P.A v)) (P.antipode v) fun _ _ ↦ Commute.all _ _).comp
      (Bialgebra.comulAlgHom R (P.A v)) =
      (Algebra.ofId R (P.A v)).comp (Bialgebra.counitAlgHom R (P.A v)) := by
  letI := P.bialgebra v
  refine P.algHom_ext_A v fun j => ?_
  change (Algebra.TensorProduct.lift (.id R (P.A v)) (P.antipode v)
    fun _ _ ↦ Commute.all _ _) (P.comul v (P.t v j)) =
    algebraMap R (P.A v) (P.counit v (P.t v j))
  rw [comul_t, counit_t, map_zero, wΔ,
    P.addE_map _ (P.tnf_tL v) (P.tnf_tR v) (x' := P.t v)
      (y' := P.F.mulE 𝔪R (p ^ v - 1) (P.t v)) (fun k => by simp [tL])
      (fun k => by simp [tR, antipode_t]) j,
    FGL.addE_comm _ (P.tnf_t v) (P.tnf_neg v), addE_neg]
  rfl

/-- The Hopf algebra structure on `A_v`. -/
abbrev hopfAlgebra (v : ℕ) : HopfAlgebra R (P.A v) :=
  letI := P.bialgebra v
  HopfAlgebra.ofAlgHom (P.antipode v) (P.antipode_left v) (P.antipode_right v)

theorem isCocomm (v : ℕ) :
    letI := P.hopfAlgebra v
    Coalgebra.IsCocomm R (P.A v) := by
  letI := P.hopfAlgebra v
  refine ⟨LinearMap.ext fun a => ?_⟩
  have := congrArg (fun φ => φ a) (P.comm_comul v)
  exact this

/-- **The finite flat commutative group scheme `F[p^v]`** ([Hong, Prop. 2.2.10 (1)]). -/
abbrev groupScheme (v : ℕ) : FFGroupScheme R :=
  letI := P.hopfAlgebra v
  haveI := P.isCocomm v
  { A := P.A v }

/-- `F[p^v]` has order `p^{hv}`. -/
theorem order_groupScheme (v : ℕ) : (P.groupScheme v).order = p ^ (P.height * v) :=
  FGL.finrank_layer P.isPDivisible v

end PDivFGL

end PadicHodge
