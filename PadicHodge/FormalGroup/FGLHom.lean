/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.FormalGroup.LayerPDiv
import PadicHodge.GroupScheme.PDivisibleHom

/-!
# Homomorphisms of formal group laws and of their `p`-divisible groups

A homomorphism of formal group laws `F → F'` (dimensions `d`, `d'`) is a family
`f ∈ R[[T_1, …, T_d]]^{d'}` without constant terms with `f(Φ_F(T, U)) = Φ_{F'}(f(T), f(U))`
(`FGL.Hom`; [Hong, §2.2] uses these morphisms in the Serre–Tate equivalence, Thm. 2.2.16).

* `FGL.Hom.fE`: evaluation of `f` at topologically nilpotent families in complete algebras;
  it is additive (`fE_addE`) and commutes with `[n]` (`fE_mulE`) and with algebra maps
  (`fE_comp`);
* for `p`-divisible formal group laws `P`, `P'`: the bialgebra maps `A'_v → A_v`,
  `t' ↦ f(t)` (`layerMap`, `layerHom`), compatible with the closed immersions: **the
  homomorphism of `p`-divisible groups `F[p^∞] → F'[p^∞]`** (`FGL.Hom.toPDiv`), i.e. the
  functor `F ↦ F[p^∞]` of [Hong, Prop. 2.2.10, Thm. 2.2.16] on morphisms.
-/

noncomputable section

open MvPowerSeries IsLocalRing PadicHodge.AdicEval TensorProduct

namespace PadicHodge

universe u

namespace FGL

variable {R : Type*} [CommRing R] {d d' : ℕ}

/-- **A homomorphism of formal group laws** `F → F'`: `f(Φ(T, U)) = Φ'(f(T), f(U))`. -/
structure Hom (F : FGL R d) (F' : FGL R d') where
  /-- the power series `f_k(T)` -/
  f : Fin d' → MvPowerSeries (Fin d) R
  noConst : ∀ k, constantCoeff (f k) = 0
  map_add : ∀ k, (f k).subst (F.addPS (Xv (R := R) (n := 2) 0) (Xv 1)) =
    F'.addPS (fun l => (f l).subst (Xv (R := R) (d := d) (n := 2) 0))
      (fun l => (f l).subst (Xv (R := R) (d := d) (n := 2) 1)) k

namespace Hom

variable {F : FGL R d} {F' : FGL R d'} (φ : Hom F F') (𝔪 : Ideal R) {S : Type*} [CommRing S]
  [Algebra R S] [IsAdicComplete (𝔪.map (algebraMap R S)) S]

/-- `x ↦ f(x)` on topologically nilpotent families. -/
def fE (x : Fin d → S) : Fin d' → S := fun k => evF 𝔪 x (φ.f k)

variable {𝔪}

theorem tnf_fE {x : Fin d → S} (hx : TNF 𝔪 x) : TNF 𝔪 (φ.fE 𝔪 x) :=
  fun k => topNil_evF hx (φ.noConst k)

theorem fE_zero : φ.fE 𝔪 (0 : Fin d → S) = 0 := by
  funext k
  rw [fE, evF_zero_fam, φ.noConst k, map_zero]
  rfl

theorem constantCoeff_subst_Xv (a : Fin 2) (l : Fin d') :
    constantCoeff ((φ.f l).subst (Xv (R := R) (d := d) (n := 2) a)) = 0 :=
  constantCoeff_subst_eq_zero (hasSubst_of_noConst (noConst_Xv a)) (noConst_Xv a) (φ.noConst l)

theorem evF_subst_Xv {x y : Fin d → S} (hx : TNF 𝔪 x) (hy : TNF 𝔪 y) (a : Fin 2) (l : Fin d') :
    evF 𝔪 (pairS x y) ((φ.f l).subst (Xv (R := R) (d := d) (n := 2) a)) =
      evF 𝔪 (if a = 0 then x else y) (φ.f l) := by
  rw [evF_subst (tnf_pairS hx hy) (noConst_Xv a)]
  congr 1
  funext j
  rw [evF_pairS_Xv hx hy]
  split_ifs <;> rfl

/-- **`f(x +_F y) = f(x) +_{F'} f(y)`.** -/
theorem fE_addE {x y : Fin d → S} (hx : TNF 𝔪 x) (hy : TNF 𝔪 y) :
    φ.fE 𝔪 (F.addE 𝔪 x y) = F'.addE 𝔪 (φ.fE 𝔪 x) (φ.fE 𝔪 y) := by
  funext k
  have h := congrArg (evF 𝔪 (pairS x y)) (φ.map_add k)
  rw [evF_subst (tnf_pairS hx hy) (F.noConst_addPS (noConst_Xv 0) (noConst_Xv 1)),
    F'.evF_addPS (tnf_pairS hx hy) (φ.constantCoeff_subst_Xv 0) (φ.constantCoeff_subst_Xv 1)] at h
  have e1 : (fun j => evF 𝔪 (pairS x y) (F.addPS (Xv (R := R) (n := 2) 0) (Xv 1) j)) =
      F.addE 𝔪 x y := by
    funext j
    rw [F.evF_addPS (tnf_pairS hx hy) (noConst_Xv 0) (noConst_Xv 1)]
    congr 1 <;> funext i <;> rw [evF_pairS_Xv hx hy] <;> simp
  rw [e1] at h
  simp only [φ.evF_subst_Xv hx hy, show (1 : Fin 2) ≠ 0 from by decide, if_false] at h
  exact h

theorem fE_mulE (n : ℕ) {x : Fin d → S} (hx : TNF 𝔪 x) :
    φ.fE 𝔪 (F.mulE 𝔪 n x) = F'.mulE 𝔪 n (φ.fE 𝔪 x) := by
  induction n with
  | zero => rw [F.mulE_zero, F'.mulE_zero, fE_zero]
  | succ n ih =>
    rw [F.mulE_succ n hx, F'.mulE_succ n (φ.tnf_fE hx), φ.fE_addE (F.tnf_mulE n hx) hx, ih]

theorem fE_comp {S' : Type*} [CommRing S'] [Algebra R S']
    [IsAdicComplete (𝔪.map (algebraMap R S')) S'] (g : S →ₐ[R] S') {x : Fin d → S}
    (hx : TNF 𝔪 x) (k : Fin d') : g (φ.fE 𝔪 x k) = φ.fE 𝔪 (fun j => g (x j)) k :=
  evF_comp g hx (φ.f k)

end Hom

end FGL

namespace FGL.Hom

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsAdicComplete (maximalIdeal R) R]
  {d d' p : ℕ} [hp : Fact p.Prime] {P : PDivFGL R d p} {P' : PDivFGL R d' p}
  (φ : FGL.Hom P.F P'.F)

attribute [local instance] PDivFGL.isAdicComplete_free

local notation "𝔪R" => maximalIdeal R

/-- `A'_v → A_v`, `t' ↦ f(t)`. -/
def layerMap (v : ℕ) : P'.A v →ₐ[R] P.A v :=
  P'.liftL v (evalT (φ.fE 𝔪R (P.t v)) (φ.tnf_fE (P.tnf_t v))) fun k => by
    rw [← FGL.evF_of (φ.tnf_fE (P.tnf_t v))]
    change P'.F.mulE 𝔪R (p ^ v) (φ.fE 𝔪R (P.t v)) k = 0
    rw [← φ.fE_mulE _ (P.tnf_t v), P.mulE_t, φ.fE_zero]
    rfl

theorem layerMap_t (v : ℕ) (k : Fin d') : φ.layerMap v (P'.t v k) = φ.fE 𝔪R (P.t v) k := by
  rw [layerMap, PDivFGL.liftL_t, evalT_X]

theorem counit_layerMap (v : ℕ) : (P.counit v).comp (φ.layerMap v) = P'.counit v := by
  refine P'.algHom_ext_A v fun k => ?_
  rw [AlgHom.comp_apply, layerMap_t, φ.fE_comp _ (P.tnf_t v), PDivFGL.counit_t]
  simp only [PDivFGL.counit_t]
  exact congrFun φ.fE_zero k

theorem comul_layerMap (v : ℕ) :
    (Algebra.TensorProduct.map (φ.layerMap v) (φ.layerMap v)).comp (P'.comul v) =
      (P.comul v).comp (φ.layerMap v) := by
  refine P'.algHom_ext_A v fun k => ?_
  rw [AlgHom.comp_apply, AlgHom.comp_apply, PDivFGL.comul_t, layerMap_t,
    φ.fE_comp _ (P.tnf_t v)]
  simp only [PDivFGL.comul_t]
  rw [PDivFGL.wΔ, PDivFGL.wΔ, P'.addE_map _ (P'.tnf_tL v) (P'.tnf_tR v)
    (x' := φ.fE 𝔪R (P.tL v)) (y' := φ.fE 𝔪R (P.tR v)), ← φ.fE_addE (P.tnf_tL v) (P.tnf_tR v)]
  · intro l
    simp only [PDivFGL.tL, Algebra.TensorProduct.map_tmul, map_one, layerMap_t]
    exact φ.fE_comp (Algebra.TensorProduct.includeLeft (S := R) (R := R) (A := P.A v)
      (B := P.A v)) (P.tnf_t v) l
  · intro l
    simp only [PDivFGL.tR, Algebra.TensorProduct.map_tmul, map_one, layerMap_t]
    exact φ.fE_comp (Algebra.TensorProduct.includeRight (R := R) (A := P.A v) (B := P.A v))
      (P.tnf_t v) l

/-- **The homomorphism `F[p^v] → F'[p^v]`.** -/
def layerHom (v : ℕ) : FFGroupScheme.Hom (P.groupScheme v) (P'.groupScheme v) :=
  letI := P.hopfAlgebra v
  letI := P'.hopfAlgebra v
  BialgHom.ofAlgHom (φ.layerMap v) (φ.counit_layerMap v) (φ.comul_layerMap v)

theorem layerHom_apply (v : ℕ) (a : P'.A v) : φ.layerHom v a = φ.layerMap v a := rfl

theorem layerIncl_layerMap (v : ℕ) :
    (P.F.layerIncl p v).comp (φ.layerMap (v + 1)) = (φ.layerMap v).comp (P'.F.layerIncl p v) := by
  refine P'.algHom_ext_A (v + 1) fun k => ?_
  rw [AlgHom.comp_apply, AlgHom.comp_apply, layerMap_t, PDivFGL.layerIncl_t, layerMap_t,
    φ.fE_comp _ (P.tnf_t (v + 1))]
  simp only [PDivFGL.layerIncl_t]

/-- **The homomorphism of `p`-divisible groups `F[p^∞] → F'[p^∞]`** induced by `f : F → F'`. -/
def toPDiv : PDivGroup.Hom P.pdivGroup P'.pdivGroup where
  f := φ.layerHom
  comm v := BialgHom.coe_toAlgHom_injective (φ.layerIncl_layerMap v)

end FGL.Hom

end PadicHodge
