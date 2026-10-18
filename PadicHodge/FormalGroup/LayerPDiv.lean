/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.FormalGroup.LayerHopf
import PadicHodge.GroupScheme.PDivisible
import PadicHodge.GroupScheme.Connected

/-!
# The connected `p`-divisible group `F[p^∞]` ([Hong, Prop. 2.2.10 (2)])

For a `p`-divisible formal group law `F` of height `h` over a complete local ring `R`
(`PDivFGL`), the group schemes `F[p^v] = Spec A_v` (`FormalGroup/LayerHopf.lean`) with the closed
immersions `A_{v+1} ↠ A_v` form a `p`-divisible group of height `h` (`PDivFGL.pdivGroup`):

* `incl`: `A_{v+1} ↠ A_v` is a bialgebra map (on `t`: `Φ(t ⊗ 1, 1 ⊗ t) ↦ Φ(t ⊗ 1, 1 ⊗ t)`);
* `pow_eq`: the `n`-th convolution power of a point `y : A_v → S` is `y ∘ [n]^*`, where
  `[n]^* : A_v → A_v`, `t ↦ [n]_F(t)` (`mulMap`), for every `R`-algebra `S`;
* `isConnected_groupScheme`: each `F[p^v]` is connected (`A_v` is local);
* `range_eq`: `y ∈ G_{v+1}(S)` factors through `A_{v+1} ↠ A_v` iff `y^{p^v} = 1`
  (`y` kills `[p^v]_F(t)` iff `y ∘ [p^v]^* = ε`).
-/

noncomputable section

open MvPowerSeries IsLocalRing PadicHodge.AdicEval TensorProduct WithConv

namespace PadicHodge

universe u

namespace PDivFGL

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsAdicComplete (maximalIdeal R) R]
  {d p : ℕ} [hp : Fact p.Prime] (P : PDivFGL R d p)

attribute [local instance] isAdicComplete_free

local notation "𝔪R" => maximalIdeal R

omit [IsLocalRing R] [IsAdicComplete (maximalIdeal R) R] hp in
theorem layerIncl_t (v : ℕ) (j : Fin d) : P.F.layerIncl p v (P.t (v + 1) j) = P.t v j := by
  rw [t, t, FGL.layerIncl, Ideal.Quotient.factorₐ_apply_mk]

omit [IsLocalRing R] [IsAdicComplete (maximalIdeal R) R] hp in
theorem layerIncl_mk (v : ℕ) (f : MvPowerSeries (Fin d) R) :
    P.F.layerIncl p v (Ideal.Quotient.mk _ f) = Ideal.Quotient.mk _ f := by
  rw [FGL.layerIncl, Ideal.Quotient.factorₐ_apply_mk]

theorem incl_counit (v : ℕ) :
    (P.counit v).comp (P.F.layerIncl p v) = P.counit (v + 1) := by
  refine P.algHom_ext_A (v + 1) fun j => ?_
  rw [AlgHom.comp_apply, layerIncl_t, counit_t, counit_t]

theorem incl_comul (v : ℕ) :
    (Algebra.TensorProduct.map (P.F.layerIncl p v) (P.F.layerIncl p v)).comp (P.comul (v + 1)) =
      (P.comul v).comp (P.F.layerIncl p v) := by
  refine P.algHom_ext_A (v + 1) fun j => ?_
  rw [AlgHom.comp_apply, AlgHom.comp_apply, comul_t, layerIncl_t, comul_t, wΔ, wΔ]
  exact P.addE_map _ (P.tnf_tL (v + 1)) (P.tnf_tR (v + 1))
    (fun k => by simp [tL, layerIncl_t]) (fun k => by simp [tR, layerIncl_t]) j

/-- **The closed immersion `F[p^v] ↪ F[p^{v+1}]`**, a homomorphism of group schemes. -/
def incl (v : ℕ) : FFGroupScheme.Hom (P.groupScheme v) (P.groupScheme (v + 1)) :=
  letI := P.hopfAlgebra v
  letI := P.hopfAlgebra (v + 1)
  BialgHom.ofAlgHom (P.F.layerIncl p v) (P.incl_counit v) (P.incl_comul v)

theorem incl_apply (v : ℕ) (a : P.A (v + 1)) : P.incl v a = P.F.layerIncl p v a := rfl

/-! ### Multiplication by `n` -/

/-- `[n]^* : A_v → A_v`, `t ↦ [n]_F(t)`. -/
def mulMap (v n : ℕ) : P.A v →ₐ[R] P.A v :=
  P.liftL v (evalT _ (P.F.tnf_mulE n (P.tnf_t v))) fun j => by
    rw [← FGL.evF_of (P.F.tnf_mulE n (P.tnf_t v))]
    change P.F.mulE 𝔪R (p ^ v) (P.F.mulE 𝔪R n (P.t v)) j = 0
    rw [FGL.mulE_mulE _ _ _ (P.tnf_t v), mul_comm, ← FGL.mulE_mulE _ _ _ (P.tnf_t v), mulE_t,
      FGL.mulE_zero_fam]
    rfl

theorem mulMap_t (v n : ℕ) (j : Fin d) : P.mulMap v n (P.t v j) = P.F.mulE 𝔪R n (P.t v) j := by
  rw [mulMap, liftL_t, evalT_X]

theorem mulMap_zero (v : ℕ) : P.mulMap v 0 = (Algebra.ofId R (P.A v)).comp (P.counit v) := by
  refine P.algHom_ext_A v fun j => ?_
  rw [mulMap_t, FGL.mulE_zero, AlgHom.comp_apply, counit_t, map_zero]
  rfl

theorem mulMap_succ (v n : ℕ) :
    (Algebra.TensorProduct.lmul' R).comp
      ((Algebra.TensorProduct.map (P.mulMap v n) (.id R (P.A v))).comp (P.comul v)) =
      P.mulMap v (n + 1) := by
  refine P.algHom_ext_A v fun j => ?_
  rw [AlgHom.comp_apply, AlgHom.comp_apply, comul_t, mulMap_t, FGL.mulE_succ _ _ (P.tnf_t v),
    wΔ]
  have := P.addE_map ((Algebra.TensorProduct.lmul' R).comp
    (Algebra.TensorProduct.map (P.mulMap v n) (.id R (P.A v)))) (P.tnf_tL v) (P.tnf_tR v)
    (x' := P.F.mulE 𝔪R n (P.t v)) (y' := P.t v) (fun k => by simp [tL, mulMap_t])
    (fun k => by simp [tR]) j
  simpa only [AlgHom.comp_apply] using this

/-- **Convolution powers**: `y^n = y ∘ [n]^*`. -/
theorem pow_eq (v : ℕ) (S : Type u) [CommRing S] [Algebra R S]
    (y : (P.groupScheme v).points S) (n : ℕ) :
    y ^ n = toConv ((ofConv y).comp (P.mulMap v n)) := by
  letI := P.hopfAlgebra v
  induction n with
  | zero =>
    rw [pow_zero, mulMap_zero]
    apply WithConv.ofConv_injective
    ext a
    change algebraMap R S (P.counit v a) = (ofConv y) (algebraMap R (P.A v) (P.counit v a))
    exact ((ofConv y).commutes (P.counit v a)).symm
  | succ n ih =>
    rw [pow_succ, ih]
    change toConv ((Algebra.TensorProduct.lmul' R).comp ((Algebra.TensorProduct.map
      ((ofConv y).comp (P.mulMap v n)) (ofConv y)).comp (P.comul v))) = _
    rw [← mulMap_succ]
    congr 1
    set g : P.A v →ₐ[R] S := ofConv y with hg
    have e : (Algebra.TensorProduct.lmul' R).comp (Algebra.TensorProduct.map
        (g.comp (P.mulMap v n)) g) =
        g.comp ((Algebra.TensorProduct.lmul' R).comp
          (Algebra.TensorProduct.map (P.mulMap v n) (.id R (P.A v)))) := by
      ext a
      · simp
      · simp
    rw [← AlgHom.comp_assoc, e]
    rfl

theorem incl_mulMap (v : ℕ) :
    (P.F.layerIncl p v).comp (P.mulMap (v + 1) (p ^ v)) =
      (Algebra.ofId R (P.A v)).comp (P.counit (v + 1)) := by
  refine P.algHom_ext_A (v + 1) fun j => ?_
  rw [AlgHom.comp_apply, mulMap_t, AlgHom.comp_apply, counit_t, map_zero]
  have := FGL.mulE_comp P.F (P.F.layerIncl p v) (p ^ v) (P.tnf_t (v + 1)) j
  rw [this]
  simp only [layerIncl_t]
  rw [mulE_t]
  rfl

/-- **`F[p^v] = F[p^{v+1}][p^v]` on points.** -/
theorem range_eq (v : ℕ) (S : Type u) [CommRing S] [Algebra R S]
    (y : (P.groupScheme (v + 1)).points S) :
    (∃ x, (P.incl v).mapPoints S x = y) ↔ y ^ (p ^ v) = 1 := by
  letI := P.hopfAlgebra v
  letI := P.hopfAlgebra (v + 1)
  constructor
  · rintro ⟨x, rfl⟩
    rw [pow_eq]
    apply WithConv.ofConv_injective
    ext a
    change (ofConv x) (P.F.layerIncl p v (P.mulMap (v + 1) (p ^ v) a)) =
      algebraMap R S (P.counit (v + 1) a)
    have := congrArg (fun φ => φ a) (P.incl_mulMap v)
    simp only [AlgHom.comp_apply, Algebra.ofId_apply] at this
    rw [this]
    exact (ofConv x).commutes _
  · intro hy
    rw [pow_eq] at hy
    have hy' : (ofConv y).comp (P.mulMap (v + 1) (p ^ v)) =
        (Algebra.ofId R S).comp (P.counit (v + 1)) := congrArg ofConv hy
    have hk : ∀ j, ((ofConv y).comp (Ideal.Quotient.mkₐ R _)) (P.F.mulPS (p ^ v) j) = 0 := by
      intro j
      have h1 := congrArg (fun φ => φ (P.t (v + 1) j)) hy'
      simp only [AlgHom.comp_apply] at h1
      have h2 : P.F.mulE 𝔪R (p ^ v) (P.t (v + 1)) j =
          Ideal.Quotient.mk _ (P.F.mulPS (p ^ v) j) := P.evF_t (v + 1) _
      rw [mulMap_t, counit_t, map_zero, h2] at h1
      exact h1
    refine ⟨toConv (P.liftL v ((ofConv y).comp (Ideal.Quotient.mkₐ R _)) hk), ?_⟩
    apply WithConv.ofConv_injective
    change (P.liftL v _ hk).comp (P.F.layerIncl p v) = ofConv y
    apply Ideal.Quotient.algHom_ext R
    ext f
    simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, layerIncl_mk, liftL_mk]
    try rfl

/-- **`F[p^v]` is connected**: `A_v` is a quotient of the local ring `R[[T]]`. -/
theorem isConnected_groupScheme (v : ℕ) : (P.groupScheme v).IsConnected := by
  haveI := P.nontrivial_A v
  exact IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective

/-- **The connected `p`-divisible group `F[p^∞]`** of a `p`-divisible formal group law
([Hong, Prop. 2.2.10 (2)]). -/
abbrev pdivGroup : PDivGroup R p where
  height := P.height
  G := P.groupScheme
  order_eq := P.order_groupScheme
  incl := P.incl
  incl_surjective v := P.F.layerIncl_surjective p v
  range_eq := P.range_eq

end PDivFGL

end PadicHodge
