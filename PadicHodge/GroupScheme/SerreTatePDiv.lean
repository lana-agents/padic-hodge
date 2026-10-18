/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.GroupScheme.SerreTateFGL
import PadicHodge.GroupScheme.SpecialFibre

/-!
# Serre–Tate, essential surjectivity: `p`-divisibility and `F[p^∞] ≅ H`

Let `H` be a connected `p`-divisible group over a coefficient ring `R` (`SerreTate.CoeffRing`,
e.g. `ℤ_p`, `O_{K'}`) with coordinates `C : Coords H d`
(`GroupScheme/SerreTateFGL.lean`), `F = C.fgl` the formal group law of `H` and
`f_v : R[[T]] ↠ A_v`, `T ↦ y_v`. Following [Hong, Thm. 2.2.16, proof, last paragraph]:

* `Coords.ev_mulPS`: `f_v([n]_F(T)) = y^{*n}` (convolution power of the universal point), so
  `f_v` kills `[p^v]_F(T)` (`G_v` is killed by `p^v`), and `f_{v+1} ∘ [p]_F^* = quot_v^* ∘ f_v`
  (`Coords.ev_pSubst`, from `i_v ∘ quot_v = [p]`);
* `PDivGroup.ker_toOne_le`: `ker(A_{v+1} ↠ A_1) ⊆ quot_v^*(I_v) A_{v+1}` (Yoneda: the kernel of
  `quot_v` is killed by `p`, hence lies in `G_1`);
* `Coords.ThetaL_bijective`: if `b_j ∈ R[[T]]` lift an `R`-basis of `A_1`, then
  `A_v^{p^h} → A_{v+1}`, `c ↦ ∑ quot_v^*(c_j) f_{v+1}(b_j)`, is bijective (Nakayama over the local
  ring `A_v`, then ranks: `|G_{v+1}| = p^h |G_v|`);
* **`Coords.isPDivisible`**: `R[[T]]` is free of rank `p^h` over itself via `[p]_F^*` with basis
  `(b_j)` (pass to the limit with `R[[T]] ≅ lim_v A_v`) — "it is then straightforward to check
  that `[p]_μ` is finite flat" in [Hong];
* **`Coords.pdivHom`**: the bialgebra maps `R[[T]]/[p^v]_F(I) → A_v` induced by `f_v` form a
  homomorphism `H → F[p^∞]`, bijective at every level (surjective between free modules of the
  same rank `p^{hv}`), with inverse `Coords.pdivHomInv`; **`Coords.exists_iso`**.
-/

noncomputable section

open MvPowerSeries IsLocalRing PadicHodge.AdicEval TensorProduct WithConv Module

namespace PadicHodge

/-! ### The kernel of `A_{v+1} ↠ A_1` -/

namespace PDivGroup

universe u

variable {R : Type u} [CommRing R] {p : ℕ} (H : PDivGroup R p)

/-- The iterated transition map `A_{w+1} ↠ A_1`. -/
def toOne : ∀ w : ℕ, (H.G (w + 1)).A →ₐ[R] (H.G 1).A
  | 0 => AlgHom.id R _
  | w + 1 => (toOne w).comp (H.incl (w + 1) : (H.G (w + 1 + 1)).A →ₐ[R] (H.G (w + 1)).A)

theorem toOne_succ_apply (w : ℕ) (a : (H.G (w + 1 + 1)).A) :
    H.toOne (w + 1) a = H.toOne w (H.incl (w + 1) a) := rfl

/-- **Yoneda**: a point of `G_{w+1}` killed by `p` comes from `G_1`. -/
theorem exists_eq_comp_toOne (w : ℕ) {B : Type u} [CommRing B] [Algebra R B]
    (x : (H.G (w + 1)).points B) (hx : x ^ p = 1) :
    ∃ x₁ : (H.G 1).A →ₐ[R] B, ofConv x = x₁.comp (H.toOne w) := by
  induction w with
  | zero => exact ⟨ofConv x, rfl⟩
  | succ w ih =>
    obtain ⟨x', hx'⟩ := (H.range_eq (w + 1) B x).mpr (by rw [pow_succ', pow_mul, hx, one_pow])
    have hp' : x' ^ p = 1 := by
      apply H.mapPoints_injective (w + 1) B
      rw [map_pow, hx', hx, map_one]
    obtain ⟨x₁, h₁⟩ := ih x' hp'
    refine ⟨x₁, ?_⟩
    rw [← hx']
    change (ofConv x').comp _ = _
    rw [h₁]
    rfl

/-- **`ker(A_{v+1} ↠ A_1) ⊆ quot_v^*(I_v) A_{v+1}`**: the kernel of `quot_v` lies in `G_1`. -/
theorem ker_toOne_le (v : ℕ) :
    RingHom.ker (H.toOne v) ≤ Ideal.map (H.quotAlg v) (counitKer R (H.G v).A) := by
  set I := Ideal.map (H.quotAlg v) (counitKer R (H.G v).A)
  let x := Ideal.Quotient.mkₐ R I
  have h1 : (H.quot v).mapPoints _ (toConv x) = 1 := by
    apply WithConv.ofConv_injective
    ext a
    change x (H.quot v a) = ofConv (1 : (H.G v).points ((H.G (v + 1)).A ⧸ I)) a
    rw [AlgHom.convOne_apply, Ideal.Quotient.mkₐ_eq_mk]
    have hc' : Coalgebra.counit (R := R) (H.quot v a) = Coalgebra.counit (R := R) a :=
      CoalgHomClass.counit_comp_apply _ a
    rw [← hc']
    refine mk_eq_algebraMap_counit I ?_
    rw [hc', quot_apply, ← AlgHom.commutes (H.quotAlg v), ← map_sub]
    exact Ideal.mem_map_of_mem _ (mem_counitKer.mpr (counit_sub_algebraMap a))
  have h2 : (toConv x : (H.G (v + 1)).points _) ^ p = 1 := by
    rw [← H.incl_quot v (toConv x), h1, map_one]
  obtain ⟨x₁, hx₁⟩ := H.exists_eq_comp_toOne v (toConv x) h2
  intro a ha
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  have := congrArg (fun φ : (H.G (v + 1)).A →ₐ[R] _ => φ a) hx₁
  simp only [AlgHom.comp_apply, RingHom.mem_ker.mp ha, map_zero] at this
  exact this

end PDivGroup

namespace SerreTate

/-- **A surjective linear map between free modules of the same finite rank is bijective.** -/
theorem bijective_of_surjective_of_finrank_eq {R M N : Type*} [CommRing R] [Nontrivial R]
    [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M]
    [AddCommGroup N] [Module R N] [Module.Free R N] [Module.Finite R N]
    (f : M →ₗ[R] N) (hf : Function.Surjective f) (h : finrank R M = finrank R N) :
    Function.Bijective f := by
  refine ⟨?_, hf⟩
  let e : N ≃ₗ[R] M := (Module.finBasis R N).equiv (Module.finBasis R M) (finCongr h.symm)
  have := OrzechProperty.injective_of_surjective_endomorphism (e.toLinearMap ∘ₗ f)
    (e.surjective.comp hf)
  exact Function.Injective.of_comp (f := e) this

/-- Homomorphisms of `p`-divisible groups are determined by their levels. -/
theorem hom_ext {R : Type*} [CommRing R] {p : ℕ} {G H : PDivGroup R p}
    {φ ψ : PDivGroup.Hom G H} (h : φ.f = ψ.f) : φ = ψ := by
  cases φ; cases ψ; cases h; rfl

variable {R : Type} [CommRing R] [IsLocalRing R] [IsAdicComplete (maximalIdeal R) R]
  [CoeffRing R] {p : ℕ}

local notation "𝔪p" => maximalIdeal R

attribute [local instance] PDivFGL.isAdicComplete_free

namespace Coords

variable {H : PDivGroup R p} {d : ℕ} (C : Coords H d)

/-! ### Multiplication by `n` -/

/-- **`[n]_F(y) = y^{*n}`.** -/
theorem mulE_y (v n : ℕ) :
    C.fgl.mulE 𝔪p n (C.y v) = fun j => ofConv ((H.G v).univPt ^ n) (C.y v j) := by
  induction n with
  | zero =>
    rw [FGL.mulE_zero, pow_zero]
    funext j
    rw [AlgHom.convOne_apply, C.counit_y, map_zero]
    rfl
  | succ n ih =>
    rw [FGL.mulE_succ _ _ (C.tnf v), ih]
    funext i
    rw [pow_succ]
    exact C.evF_conv v ((H.G v).univPt ^ n) (H.G v).univPt i

theorem ev_mulPS (v n : ℕ) (j : Fin d) :
    C.ev v (C.fgl.mulPS n j) = ofConv ((H.G v).univPt ^ n) (C.y v j) := by
  rw [ev_eq_evF]
  exact congrFun (C.mulE_y v n) j

/-- `f_v` kills `[p^v]_F(T)`. -/
theorem ev_mulPS_pow (v : ℕ) (j : Fin d) : C.ev v (C.fgl.mulPS (p ^ v) j) = 0 := by
  rw [ev_mulPS, H.pow_eq_one v _ (H.G v).univPt, AlgHom.convOne_apply, C.counit_y, map_zero]

/-- **`f_{v+1} ∘ [p]_F^* = quot_v^* ∘ f_v`.** -/
theorem ev_pSubst (v : ℕ) :
    (C.ev (v + 1)).comp (C.fgl.pSubst p) = (H.quotAlg v).comp (C.ev v) := by
  symm
  refine algHom_ext_topNil (𝔪 := 𝔪p) (fun j => ?_) fun j => ?_
  · rw [AlgHom.comp_apply, ev_X]; exact (C.tnf v j).map _
  · rw [AlgHom.comp_apply, AlgHom.comp_apply, ev_X, FGL.pSubst_apply,
      subst_X (FGL.hasSubst_of_noConst (C.fgl.noConst_mulPS p)), ← C.incl_y v j, ev_mulPS]
    exact congrArg (fun φ : (H.G (v + 1)).points (H.G (v + 1)).A => ofConv φ (C.y (v + 1) j))
      (H.incl_quotAlg v)

include C in
theorem incl_quotAlg_comm (v : ℕ) (a : (H.G (v + 1)).A) :
    H.incl (v + 1) (H.quotAlg (v + 1) a) = H.quotAlg v (H.incl v a) := by
  obtain ⟨g, rfl⟩ := C.ev_surjective (v + 1) a
  have h1 := congrArg (fun φ => φ g) (C.ev_pSubst (v + 1))
  have h2 := congrArg (fun φ => φ g) (C.ev_pSubst v)
  simp only [AlgHom.comp_apply] at h1 h2
  rw [← h1, C.incl_ev, h2, C.incl_ev]

/-! ### A basis of `A_{v+1}` over `A_v` -/

/-- An `R`-basis of `A_1`. -/
def basis1 (H : PDivGroup R p) : Module.Basis (Fin (p ^ H.height)) R (H.G 1).A :=
  Module.finBasisOfFinrankEq _ _ (by have := H.order_eq 1; rwa [mul_one] at this)

/-- Lifts `b_j ∈ R[[T]]` of the basis of `A_1`. -/
def bL (j : Fin (p ^ H.height)) : MvPowerSeries (Fin d) R :=
  (C.ev_surjective 1 (basis1 H j)).choose

omit [CoeffRing R] in
theorem ev_bL (j : Fin (p ^ H.height)) : C.ev 1 (C.bL j) = basis1 H j :=
  (C.ev_surjective 1 (basis1 H j)).choose_spec

omit [CoeffRing R] in
theorem toOne_ev (v : ℕ) (g : MvPowerSeries (Fin d) R) :
    H.toOne v (C.ev (v + 1) g) = C.ev 1 g := by
  induction v with
  | zero => rfl
  | succ v ih => rw [PDivGroup.toOne_succ_apply, C.incl_ev, ih]

/-- `Θ_v : A_v^{p^h} → A_{v+1}`, `c ↦ ∑ quot_v^*(c_j) f_{v+1}(b_j)`. -/
def ThetaL (v : ℕ) : (Fin (p ^ H.height) → (H.G v).A) →ₗ[R] (H.G (v + 1)).A where
  toFun c := ∑ j, H.quotAlg v (c j) * C.ev (v + 1) (C.bL j)
  map_add' c c' := by simp only [Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]
  map_smul' r c := by
    simp only [Pi.smul_apply, map_smul, smul_mul_assoc, Finset.smul_sum, RingHom.id_apply]

omit [CoeffRing R] in
theorem ThetaL_apply (v : ℕ) (c : Fin (p ^ H.height) → (H.G v).A) :
    C.ThetaL v c = ∑ j, H.quotAlg v (c j) * C.ev (v + 1) (C.bL j) := rfl

omit [IsAdicComplete 𝔪p R] [CoeffRing R] in
theorem counitKer_le_maximalIdeal (v : ℕ) [IsLocalRing (H.G v).A] :
    counitKer R (H.G v).A ≤ maximalIdeal (H.G v).A := by
  intro c hc
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  have := hu.map (Bialgebra.counitAlgHom R (H.G v).A)
  rw [RingHom.mem_ker.mp hc] at this
  exact not_isUnit_zero this

omit [CoeffRing R] in
/-- **`Θ_v` is surjective** (Nakayama over the local ring `A_v`). -/
theorem ThetaL_surjective (v : ℕ) (hconn : (H.G v).IsConnected) :
    Function.Surjective (C.ThetaL v) := by
  haveI : IsLocalRing (H.G v).A := hconn
  letI : Algebra (H.G v).A (H.G (v + 1)).A := (H.quotAlg v).toRingHom.toAlgebra
  haveI : IsScalarTower R (H.G v).A (H.G (v + 1)).A :=
    IsScalarTower.of_algebraMap_eq fun r => ((H.quotAlg v).commutes r).symm
  haveI : Module.Finite (H.G v).A (H.G (v + 1)).A :=
    Module.Finite.of_restrictScalars_finite R _ _
  set bb : Fin (p ^ H.height) → (H.G (v + 1)).A := fun j => C.ev (v + 1) (C.bL j)
  have key : (⊤ : Submodule (H.G v).A (H.G (v + 1)).A) ≤
      Submodule.span (H.G v).A (Set.range bb) ⊔ maximalIdeal (H.G v).A • ⊤ := by
    intro a _
    set r := (basis1 H).repr (H.toOne v a)
    set w : (H.G (v + 1)).A := ∑ j, r j • bb j
    have hw : H.toOne v w = H.toOne v a := by
      simp only [w, bb, map_sum, map_smul, C.toOne_ev, ev_bL]
      exact (basis1 H).sum_repr _
    have hmem : a - w ∈ Ideal.map (H.quotAlg v) (counitKer R (H.G v).A) :=
      H.ker_toOne_le v (by rw [RingHom.mem_ker, map_sub, hw, sub_self])
    have h1 : w ∈ Submodule.span (H.G v).A (Set.range bb) := by
      refine Submodule.sum_mem _ fun j _ => ?_
      rw [← algebraMap_smul (H.G v).A (r j) (bb j)]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
    have hle : Ideal.map (H.quotAlg v) (counitKer R (H.G v).A) ≤
        Ideal.map (algebraMap (H.G v).A (H.G (v + 1)).A) (maximalIdeal (H.G v).A) :=
      Ideal.map_le_iff_le_comap.mpr fun c hc => Ideal.mem_comap.mpr
        (Ideal.mem_map_of_mem (algebraMap (H.G v).A (H.G (v + 1)).A)
          (counitKer_le_maximalIdeal v hc))
    have h2 : a - w ∈ maximalIdeal (H.G v).A • (⊤ : Submodule (H.G v).A (H.G (v + 1)).A) := by
      rw [Ideal.smul_top_eq_map, Submodule.restrictScalars_mem]
      exact hle hmem
    have := Submodule.add_mem_sup h1 h2
    rwa [add_sub_cancel] at this
  have htop := Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top
    (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge key
  intro a
  obtain ⟨c, hc⟩ :=
    (Submodule.mem_span_range_iff_exists_fun _).mp (htop (Submodule.mem_top : a ∈ ⊤))
  refine ⟨c, ?_⟩
  rw [ThetaL_apply, ← hc]
  rfl

omit [CoeffRing R] in
theorem ThetaL_bijective (v : ℕ) (hconn : (H.G v).IsConnected) :
    Function.Bijective (C.ThetaL v) := by
  refine bijective_of_surjective_of_finrank_eq _ (C.ThetaL_surjective v hconn) ?_
  have e1 : finrank R (H.G v).A = p ^ (H.height * v) := H.order_eq v
  have e2 : finrank R (H.G (v + 1)).A = p ^ (H.height * (v + 1)) := H.order_eq (v + 1)
  rw [Module.finrank_pi_fintype R, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul, e1, e2]
  ring

/-! ### `p`-divisibility -/

theorem ev_sum_pSubst (v : ℕ) (c : Fin (p ^ H.height) → MvPowerSeries (Fin d) R) :
    C.ev (v + 1) (∑ i, (C.fgl.pSubst p).toRingHom (c i) * C.bL i) =
      C.ThetaL v (fun i => C.ev v (c i)) := by
  simp only [map_sum, map_mul, ThetaL_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  exact congrArg (fun φ => φ (c i)) (C.ev_pSubst v)

/-- **`F` is `p`-divisible of height `h`**: `R[[T]]` is free over itself via `[p]_F^*` with
basis `(b_j)`. -/
theorem isPDivisible (hconn : ∀ v, (H.G v).IsConnected) : C.fgl.IsPDivisible p H.height := by
  refine ⟨C.bL, ?_, ?_⟩
  · intro c c' hcc
    have hcc' : ∑ i, (C.fgl.pSubst p).toRingHom (c i) * C.bL i =
        ∑ i, (C.fgl.pSubst p).toRingHom (c' i) * C.bL i := hcc
    have hsum : ∑ i, (C.fgl.pSubst p).toRingHom ((c - c') i) * C.bL i = 0 := by
      simp only [Pi.sub_apply, map_sub, sub_mul, Finset.sum_sub_distrib]
      exact sub_eq_zero.mpr hcc'
    funext i
    refine sub_eq_zero.mp (C.inj _ fun v => ?_)
    have h0 : C.ThetaL v (fun i => C.ev v ((c - c') i)) = C.ThetaL v 0 := by
      rw [← C.ev_sum_pSubst, hsum, map_zero, map_zero]
    exact congrFun ((C.ThetaL_bijective v (hconn v)).1 h0) i
  · intro a
    choose c hc using fun v => (C.ThetaL_bijective v (hconn v)).2 (C.ev (v + 1) a)
    have hcompat : ∀ v i, H.incl v (c (v + 1) i) = c v i := by
      intro v i
      have : C.ThetaL v (fun i => H.incl v (c (v + 1) i)) = C.ThetaL v (c v) := by
        rw [hc v]
        have h := congrArg (fun x => H.incl (v + 1) x) (hc (v + 1))
        rw [C.incl_ev] at h
        rw [← h, ThetaL_apply, ThetaL_apply, map_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [map_mul, C.incl_quotAlg_comm, C.incl_ev]
      exact congrFun ((C.ThetaL_bijective v (hconn v)).1 this) i
    choose g hg using fun i => C.exists_ev_eq (fun v => c v i) (fun v => hcompat v i)
    refine ⟨g, sub_eq_zero.mp (C.inj _ fun w => ?_)⟩
    refine C.ev_eq_zero_of_le (Nat.le_succ w) ?_
    change C.ev (w + 1) ((∑ i, (C.fgl.pSubst p).toRingHom (g i) * C.bL i) - a) = 0
    rw [map_sub, C.ev_sum_pSubst, sub_eq_zero, ← hc w]
    congr 1
    funext i
    exact hg i w

/-- **The `p`-divisible formal group law of `H`.** -/
def pdivFGL (hconn : ∀ v, (H.G v).IsConnected) : PDivFGL R d p :=
  ⟨C.fgl, H.height, C.isPDivisible hconn⟩

/-! ### `F[p^∞] ≅ H` -/

variable [hp : Fact p.Prime] (hconn : ∀ v, (H.G v).IsConnected)

/-- `R[[T]]/[p^v]_F(I) → A_v`, `t ↦ y_v`. -/
def layerMap (v : ℕ) : (C.pdivFGL hconn).A v →ₐ[R] (H.G v).A :=
  (C.pdivFGL hconn).liftL v (C.ev v) (C.ev_mulPS_pow v)

omit hp in
theorem layerMap_mk (v : ℕ) (g : MvPowerSeries (Fin d) R) :
    C.layerMap hconn v (Ideal.Quotient.mk _ g) = C.ev v g :=
  PDivFGL.liftL_mk _ _ _ _ _

omit hp in
theorem layerMap_t (v : ℕ) (j : Fin d) :
    C.layerMap hconn v ((C.pdivFGL hconn).t v j) = C.y v j := by
  rw [layerMap, PDivFGL.liftL_t, ev_X]

theorem counit_layerMap (v : ℕ) :
    (Bialgebra.counitAlgHom R (H.G v).A).comp (C.layerMap hconn v) =
      (C.pdivFGL hconn).counit v :=
  (C.pdivFGL hconn).algHom_ext_A v fun j => by
    rw [AlgHom.comp_apply, layerMap_t, PDivFGL.counit_t, Bialgebra.counitAlgHom_apply,
      C.counit_y]

theorem comul_layerMap (v : ℕ) :
    (Algebra.TensorProduct.map (C.layerMap hconn v) (C.layerMap hconn v)).comp
      ((C.pdivFGL hconn).comul v) =
      (Bialgebra.comulAlgHom R (H.G v).A).comp (C.layerMap hconn v) := by
  refine (C.pdivFGL hconn).algHom_ext_A v fun j => ?_
  rw [AlgHom.comp_apply, AlgHom.comp_apply, PDivFGL.comul_t, layerMap_t, ← C.Φ_spec j v,
    ev2_eq_evF, PDivFGL.wΔ,
    (C.pdivFGL hconn).addE_map _ ((C.pdivFGL hconn).tnf_tL v) ((C.pdivFGL hconn).tnf_tR v)
      (x' := fun k => inL v (C.y v k))
      (y' := fun k => inR v (C.y v k)) (fun k => by simp [PDivFGL.tL, layerMap_t])
      (fun k => by simp [PDivFGL.tR, layerMap_t])]
  rfl

/-- The homomorphism `H_v → F[p^v]`. -/
def toHom (v : ℕ) : FFGroupScheme.Hom (H.G v) ((C.pdivFGL hconn).groupScheme v) :=
  letI := (C.pdivFGL hconn).hopfAlgebra v
  BialgHom.ofAlgHom (C.layerMap hconn v) (C.counit_layerMap hconn v) (C.comul_layerMap hconn v)

theorem toHom_apply (v : ℕ) (a : (C.pdivFGL hconn).A v) :
    C.toHom hconn v a = C.layerMap hconn v a := rfl

theorem layerMap_incl (v : ℕ) :
    (H.incl v : (H.G (v + 1)).A →ₐ[R] (H.G v).A).comp (C.layerMap hconn (v + 1)) =
      (C.layerMap hconn v).comp ((C.pdivFGL hconn).F.layerIncl p v) :=
  (C.pdivFGL hconn).algHom_ext_A (v + 1) fun j => by
    rw [AlgHom.comp_apply, AlgHom.comp_apply, layerMap_t, PDivFGL.layerIncl_t, layerMap_t]
    exact C.incl_y v j

/-- **The homomorphism `H → F[p^∞]`.** -/
def pdivHom : PDivGroup.Hom H (C.pdivFGL hconn).pdivGroup where
  f v := C.toHom hconn v
  comm v := BialgHom.ext fun x => congrArg (fun φ => φ x) (C.layerMap_incl hconn v)

theorem pdivHom_bijective (v : ℕ) : Function.Bijective ((C.pdivHom hconn).f v) := by
  have hs : Function.Surjective (C.layerMap hconn v) := fun a => by
    obtain ⟨g, hg⟩ := C.ev_surjective v a
    exact ⟨Ideal.Quotient.mk _ g, by rw [layerMap_mk, hg]⟩
  exact bijective_of_surjective_of_finrank_eq (C.layerMap hconn v).toLinearMap hs
    ((FGL.finrank_layer (C.pdivFGL hconn).isPDivisible v).trans (H.order_eq v).symm)

/-- The levelwise isomorphisms `A_v ≅ R[[T]]/[p^v]_F(I)` of bialgebras. -/
def levelEquiv (v : ℕ) :
    letI := (C.pdivFGL hconn).hopfAlgebra v
    (C.pdivFGL hconn).A v ≃ₐc[R] (H.G v).A :=
  letI := (C.pdivFGL hconn).hopfAlgebra v
  BialgEquiv.ofBijective ((C.pdivHom hconn).f v) (C.pdivHom_bijective hconn v)

/-- **The inverse homomorphism `F[p^∞] → H`.** -/
def pdivHomInv : PDivGroup.Hom (C.pdivFGL hconn).pdivGroup H where
  f v :=
    letI := (C.pdivFGL hconn).hopfAlgebra v
    (C.levelEquiv hconn v).symm.toBialgHom
  comm v := by
    letI := (C.pdivFGL hconn).hopfAlgebra v
    letI := (C.pdivFGL hconn).hopfAlgebra (v + 1)
    refine BialgHom.ext fun a => (C.levelEquiv hconn v).injective ?_
    have h := congrArg (fun φ => φ ((C.levelEquiv hconn (v + 1)).symm a))
      (C.layerMap_incl hconn v)
    exact (h.symm.trans (congrArg (fun x => H.incl v x)
      ((C.levelEquiv hconn (v + 1)).apply_symm_apply a))).trans
      ((C.levelEquiv hconn v).apply_symm_apply _).symm

theorem pdivHom_comp_pdivHomInv :
    (C.pdivHom hconn).comp (C.pdivHomInv hconn) = PDivGroup.Hom.id _ :=
  hom_ext (funext fun v => by
    letI := (C.pdivFGL hconn).hopfAlgebra v
    exact BialgHom.ext fun a => (C.levelEquiv hconn v).symm_apply_apply a)

theorem pdivHomInv_comp_pdivHom :
    (C.pdivHomInv hconn).comp (C.pdivHom hconn) = PDivGroup.Hom.id _ :=
  hom_ext (funext fun v => by
    letI := (C.pdivFGL hconn).hopfAlgebra v
    exact BialgHom.ext fun a => (C.levelEquiv hconn v).apply_symm_apply a)

/-- **Essential surjectivity of `F ↦ F[p^∞]`, given coordinates** ([Hong, Thm. 2.2.16]): a
connected `p`-divisible group over `R` with coordinates is isomorphic to `F[p^∞]` for a
`p`-divisible formal group law `F`. -/
theorem exists_iso (C : Coords H d) (hconn : ∀ v, (H.G v).IsConnected) :
    ∃ (P : PDivFGL R d p) (φ : PDivGroup.Hom H P.pdivGroup)
      (ψ : PDivGroup.Hom P.pdivGroup H),
      φ.comp ψ = PDivGroup.Hom.id _ ∧ ψ.comp φ = PDivGroup.Hom.id _ :=
  ⟨C.pdivFGL hconn, C.pdivHom hconn, C.pdivHomInv hconn, C.pdivHom_comp_pdivHomInv hconn,
    C.pdivHomInv_comp_pdivHom hconn⟩

end Coords

end SerreTate

end PadicHodge
