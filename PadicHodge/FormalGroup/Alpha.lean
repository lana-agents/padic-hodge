/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.FormalGroup.PointsOC
import PadicHodge.FormalGroup.LayerLimitBase
import PadicHodge.FormalGroup.LayerPoints
import PadicHodge.FormalGroup.OCAdic
import PadicHodge.GroupScheme.CartierChar

/-!
# The map `α : G(O_{ℂ_p}) → Hom(T_p(G^∨), 1 + m_{ℂ_p})` for connected `G = F[p^∞]`

([Hong, Prop. 3.4.9, proof].) Let `P` be a `p`-divisible formal group law over a complete local
ring `R` (`p ∈ 𝔪_R`, `R → O_{ℂ_p}` with `𝔪_R ↦ m_{ℂ_p}`, `O_{ℂ_p}` complete for `𝔪_R O_{ℂ_p}`;
e.g. `R = ℤ_p`), `G = F[p^∞]` with layers `G_v = Spec A_v`. Write `S = O_{ℂ_p}` (as the
discrete coefficient ring `OCd p`). For `y = (y_v) ∈ T_p(G^∨)(S) = lim_v G_v^∨(S)`
(`PDivGroup.DualTate`):

* the characters `χ_{y_v} ∈ S ⊗_R A_v` (`FFGroupScheme.charOf`) are group-like and compatible
  (`charB_incl`, `charB_comul`), so by [Hong, Lemma 2.2.15] (`PDivFGL.exists_groupLike`) there is
  a unique `U_y ∈ S[[T]]` with `U_y(t) = χ_{y_v}` in every `S ⊗ A_v` and
  `U_y(Φ(T, T')) = U_y(T) U_y(T')` (`charSeries`; this is (3.7):
  `T_p(G^∨) = Hom(F_{O_C}, Ĝ_m)`);
* **`α(x)(y) = U_y(x)`** for `x ∈ F(m_{ℂ_p}) = G(O_{ℂ_p})` (`alpha`), additive in `x`
  (`alpha_add`) and multiplicative in `y` (`alpha_mul`);
* **left square of [Hong, Prop. 3.4.9]**: for a `p^v`-torsion point `x`, `α(x)(y)` is the Cartier
  pairing `⟨x_v, y_v⟩` of the layer point `x_v ∈ G_v(O_{ℂ_p})` with `y_v` (`alpha_torsion`).
  In particular `α(0) = 1`.
-/

noncomputable section

open MvPowerSeries IsLocalRing TensorProduct WithConv

namespace PadicHodge

open FGL

/-- `O_{ℂ_p}` as an `R`-algebra via a given `R → O_{ℂ_p}` (low priority: for `R = OCd p` the
identity instance must win). -/
@[reducible, instance 10]
def OCd.algebraOf (p : ℕ) [Fact p.Prime] (R : Type*) [CommRing R] [Algebra R (OC p)] :
    Algebra R (OCd p) := ‹Algebra R (OC p)›

namespace OCd

variable {p : ℕ} [Fact p.Prime] {R : Type*} [CommRing R] [Algebra R (OC p)]

instance : IsScalarTower R (OCd p) (OC p) := IsScalarTower.of_algebraMap_eq fun _ => rfl

end OCd

namespace PDivFGL

open FFGroupScheme

variable {p : ℕ} [hp : Fact p.Prime] {R : Type} [CommRing R] [IsLocalRing R]
  [IsAdicComplete (maximalIdeal R) R] [UniformSpace R] [DiscreteUniformity R] [Algebra R (OC p)]
  {d : ℕ} (P : PDivFGL R d p)

local notation "𝔪R" => maximalIdeal R
local notation "S" => OCd p

omit [IsLocalRing R] [IsAdicComplete (maximalIdeal R) R] [UniformSpace R]
  [DiscreteUniformity R] in
/-- `Algebra.TensorProduct.map` over `S` and over `R` agree. -/
theorem map_id_eq {A B : Type} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]
    (f : A →ₐ[R] B) (z : S ⊗[R] A) :
    Algebra.TensorProduct.map (AlgHom.id S S) f z =
      Algebra.TensorProduct.map (AlgHom.id R S) f z := by
  induction z with
  | zero => simp
  | tmul s a => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy]

/-- The characters `χ_{y_v} ∈ S ⊗_R A_v` of a point `y` of the dual Tate module. -/
def charB (y : P.pdivGroup.DualTate S) (v : ℕ) : S ⊗[R] P.A v :=
  (P.groupScheme v).charOf S (y.1 v)

omit [UniformSpace R] [DiscreteUniformity R] in
theorem charB_incl (y : P.pdivGroup.DualTate S) (v : ℕ) :
    P.inclB S v (P.charB y (v + 1)) = P.charB y v := by
  rw [inclB, map_id_eq, charB, charB, y.2 v]
  exact ((P.groupScheme v).charOf_dual S (P.incl v) (y.1 (v + 1))).symm

omit [UniformSpace R] [DiscreteUniformity R] in
theorem charB_comul (y : P.pdivGroup.DualTate S) (v : ℕ) :
    P.comulB S v (P.charB y v) = P.inlB S v (P.charB y v) * P.inrB S v (P.charB y v) := by
  have h := (P.groupScheme v).charOf_comul S (y.1 v)
  rw [comulB, inlB, inrB, map_id_eq, map_id_eq, map_id_eq]
  exact h

omit [UniformSpace R] [DiscreteUniformity R] in
theorem charB_mul (y y' : P.pdivGroup.DualTate S) (v : ℕ) :
    P.charB (y * y') v = P.charB y v * P.charB y' v :=
  (P.groupScheme v).charOf_mul S _ _

variable [hC : IsAdicComplete ((maximalIdeal R).map (algebraMap R (OC p))) (OC p)]

instance isAdicComplete_OCd : IsAdicComplete ((maximalIdeal R).map (algebraMap R S)) S := hC

variable (hpm : (p : R) ∈ maximalIdeal R)

/-- **The power series `U_y ∈ O_{ℂ_p}[[T]]` of `y ∈ T_p(G^∨)`**: `U_y(t) = χ_{y_v}` in each
`S ⊗ A_v`, and `U_y(Φ(T, T')) = U_y(T) U_y(T')`. -/
def charSeries (y : P.pdivGroup.DualTate S) : MvPowerSeries (Fin d) S :=
  (P.exists_groupLike S hpm (P.charB y) (P.charB_incl y) (P.charB_comul y)).choose

omit [UniformSpace R] [DiscreteUniformity R] in
theorem evB_charSeries (y : P.pdivGroup.DualTate S) (v : ℕ) :
    P.evB S v (P.charSeries hpm y) = P.charB y v :=
  (P.exists_groupLike S hpm (P.charB y) (P.charB_incl y) (P.charB_comul y)).choose_spec.1 v

omit [UniformSpace R] [DiscreteUniformity R] in
theorem charSeries_groupLike (y : P.pdivGroup.DualTate S) :
    (P.charSeries hpm y).subst (fun j => MvPowerSeries.map (algebraMap R S) (P.F.Φ j)) =
      (P.charSeries hpm y).subst (Xv (R := S) (d := d) (n := 2) 0) *
        (P.charSeries hpm y).subst (Xv (R := S) (d := d) (n := 2) 1) :=
  (P.exists_groupLike S hpm (P.charB y) (P.charB_incl y) (P.charB_comul y)).choose_spec.2

omit [UniformSpace R] [DiscreteUniformity R] in
/-- `U_y` is determined by its images in the `S ⊗ A_v`. -/
theorem charSeries_unique (y : P.pdivGroup.DualTate S) (U : MvPowerSeries (Fin d) S)
    (hU : ∀ v, P.evB S v U = P.charB y v) : U = P.charSeries hpm y :=
  sub_eq_zero.mp (P.eq_zero_of_evB S hpm fun v => by
    rw [map_sub, hU, evB_charSeries, sub_self])

omit [UniformSpace R] [DiscreteUniformity R] in
theorem charSeries_mul (y y' : P.pdivGroup.DualTate S) :
    P.charSeries hpm (y * y') = P.charSeries hpm y * P.charSeries hpm y' :=
  (P.charSeries_unique hpm (y * y') _ fun v => by
    rw [map_mul, evB_charSeries, evB_charSeries, charB_mul]).symm

/-- **`α(x)(y) = U_y(x)`** ([Hong, Prop. 3.4.9, proof]). -/
def alpha (x : P.F.Pt p) (y : P.pdivGroup.DualTate S) : OC p :=
  FGL.ev p (P.charSeries hpm y) x.1

theorem alpha_add (x x' : P.F.Pt p) (y : P.pdivGroup.DualTate S) :
    P.alpha hpm (x + x') y = P.alpha hpm x y * P.alpha hpm x' y :=
  P.F.ev_add_of_groupLike (algebraMap R S) (fun _ => rfl) _ (P.charSeries_groupLike hpm y) x x'

omit [UniformSpace R] [DiscreteUniformity R] in
theorem alpha_mul (x : P.F.Pt p) (y y' : P.pdivGroup.DualTate S) :
    P.alpha hpm x (y * y') = P.alpha hpm x y * P.alpha hpm x y' := by
  rw [alpha, charSeries_mul]
  exact FGL.ev_mul x.2 _ _

/-! ### Torsion points: the left square -/

/-- A point `A_v → O_{ℂ_p}` viewed with values in `OCd p`. -/
def toOCd {A : Type} [CommRing A] [Algebra R A] (g : A →ₐ[R] OC p) : A →ₐ[R] S := g

/-- Evaluation at a formal point as an `S`-algebra map `S[[T]] → O_{ℂ_p}`. -/
def evS (x : P.F.Pt p) : MvPowerSeries (Fin d) S →ₐ[S] OC p :=
  { eval₂Hom (continuous_algebraMap_OC (p := p) (R := S)) (hasEval_of_norm_lt_one x.2) with
    commutes' := fun r => by
      change eval₂Hom (continuous_algebraMap_OC (p := p) (R := S))
        (hasEval_of_norm_lt_one x.2) (algebraMap S _ r) = _
      rw [coe_eval₂Hom (continuous_algebraMap_OC (p := p) (R := S)),
        MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
      exact eval₂_C (algebraMap S (OC p)) x.1 r }

omit [IsLocalRing R] [IsAdicComplete (maximalIdeal R) R] [UniformSpace R] [DiscreteUniformity R]
  [Algebra R (OC p)] hC in
theorem evS_apply (x : P.F.Pt p) (f : MvPowerSeries (Fin d) S) :
    P.evS x f = FGL.ev p f x.1 := by
  change eval₂Hom (continuous_algebraMap_OC (p := p) (R := S))
    (hasEval_of_norm_lt_one x.2) f = _
  rw [coe_eval₂Hom]
  rfl

omit [IsAdicComplete (maximalIdeal R) R] [UniformSpace R] [DiscreteUniformity R] hC in
include hpm in
/-- Elements of `m_{ℂ_p}` are topologically nilpotent for `𝔪_R O_{ℂ_p}`. -/
theorem topNil_OC {a : OC p} (ha : ‖(a : ℂ_[p])‖ < 1) :
    AdicEval.TopNil ((maximalIdeal R).map (algebraMap R S)) a := by
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (OC.norm_p_pos (p := p)) ha
  refine ⟨N, ?_⟩
  have h1 : a ^ N ∈ Ideal.span {(p : OC p)} := by
    have := (OC.mem_span_p_pow_iff 1 (a ^ N)).mpr
      (by rw [pow_one]; simpa only [SubmonoidClass.coe_pow, norm_pow] using hN.le)
    rwa [pow_one] at this
  have h2 : Ideal.span {(p : OC p)} ≤
      ((maximalIdeal R).map (algebraMap R S)).map (algebraMap S (OC p)) := by
    rw [Ideal.span_le, Set.singleton_subset_iff, Ideal.map_map_algebraMap]
    have := Ideal.mem_map_of_mem (algebraMap R (OC p)) hpm
    rwa [map_natCast] at this
  exact h2 h1

omit [IsLocalRing R] [IsAdicComplete (maximalIdeal R) R] [UniformSpace R]
  [DiscreteUniformity R] hC in
theorem productLeft_eq {A : Type} [CommRing A] [Algebra R A] (g : A →ₐ[R] OC p)
    (z : S ⊗[R] A) :
    Algebra.TensorProduct.productLeftAlgHom (Algebra.ofId S (OC p)) g z =
      Algebra.TensorProduct.productMap (AlgHom.id R S) (toOCd g) z := by
  induction z with
  | zero => rw [map_zero, map_zero]; rfl
  | tmul s a => rfl
  | add x y hx hy => rw [map_add, hx, hy, map_add]; rfl

omit [IsAdicComplete (maximalIdeal R) R] in
include hpm in
/-- **Evaluating `U(t) ∈ S ⊗ A_v` at the layer point of `x` is `U(x)`.** -/
theorem layerPt_evB (v : ℕ) (x : P.F.torsionBy (p := p) v) :
    (Algebra.TensorProduct.productLeftAlgHom (Algebra.ofId S (OC p)) (P.F.layerPt v x)).comp
      (P.evB S v) = P.evS x.1 := by
  haveI : IsHausdorff (((maximalIdeal R).map (algebraMap R S)).map (algebraMap S (OC p)))
      (OC p) := by
    rw [Ideal.map_map_algebraMap]; exact hC.toIsHausdorff
  have hX : ∀ j, ((Algebra.TensorProduct.productLeftAlgHom (Algebra.ofId S (OC p))
      (P.F.layerPt v x)).comp (P.evB S v)) (X j) = x.1.1 j := by
    intro j
    rw [AlgHom.comp_apply, evB_X]
    change (Algebra.ofId S (OC p)) 1 * P.F.layerPt v x (Ideal.Quotient.mk _ (X j)) = _
    rw [map_one, one_mul, FGL.layerPt_X]
  refine AdicEval.algHom_ext_topNil (𝔪 := (maximalIdeal R).map (algebraMap R S))
    (fun j => ?_) (fun j => ?_)
  · rw [hX]; exact topNil_OC hpm (x.1.2 j)
  · rw [hX, evS_apply, FGL.ev_X]

/-- **The left square of [Hong, Prop. 3.4.9]**: for a `p^v`-torsion point `x`, `α(x)(y)` is the
Cartier pairing `⟨x_v, y_v⟩` of the layer point `x_v ∈ G_v(O_{ℂ_p})` with `y_v`. -/
theorem alpha_torsion (v : ℕ) (x : P.F.torsionBy (p := p) v) (y : P.pdivGroup.DualTate S) :
    P.alpha hpm x.1 y =
      (P.groupScheme v).pairing S (toConv (toOCd (P.F.layerPt v x))) (y.1 v) := by
  rw [alpha, ← evS_apply, ← P.layerPt_evB hpm v x, AlgHom.comp_apply, evB_charSeries, charB,
    productLeft_eq]
  exact (P.groupScheme v).productMap_charOf S (toConv (toOCd (P.F.layerPt v x))) (y.1 v)

/-- `α(x)(y)` is a `p^v`-th root of unity for `p^v`-torsion `x`. -/
theorem isUnit_alpha_torsion (v : ℕ) (x : P.F.torsionBy (p := p) v)
    (y : P.pdivGroup.DualTate S) : IsUnit (P.alpha hpm x.1 y) := by
  rw [alpha_torsion, ← P.pdivGroup.levelPairing_val S v]
  exact Units.isUnit _

theorem alpha_zero (y : P.pdivGroup.DualTate S) : P.alpha hpm 0 y = 1 := by
  have h := P.alpha_add hpm 0 0 y
  rw [add_zero] at h
  have hu := P.isUnit_alpha_torsion hpm 0 ⟨0, (P.F.torsionBy 0).zero_mem⟩ y
  exact hu.mul_left_cancel (h.symm.trans (mul_one _).symm)

omit [IsLocalRing R] [IsAdicComplete (maximalIdeal R) R] [UniformSpace R]
  [DiscreteUniformity R] hC in
theorem ev_zeroPt (f : MvPowerSeries (Fin d) S) :
    FGL.ev p f (0 : Fin d → OC p) = constantCoeff f := by
  rw [FGL.ev, eval₂_eq_tsum continuous_algebraMap_OC
    (hasEval_of_norm_lt_one (fun _ => by simp)), tsum_eq_single 0]
  · simp; rfl
  · intro m hm
    obtain ⟨j, hj⟩ := Finsupp.support_nonempty_iff.mpr hm
    rw [Finsupp.prod, Finset.prod_eq_zero hj (by
      rw [Pi.zero_apply, zero_pow (Finsupp.mem_support_iff.mp hj)]), mul_zero]

/-- `U_y(0) = 1`: `U_y − 1` is a formal homomorphism `F_{O_C} → Ĝ_m`. -/
theorem constantCoeff_charSeries (y : P.pdivGroup.DualTate S) :
    constantCoeff (P.charSeries hpm y) = 1 := by
  have h := P.alpha_zero hpm y
  rw [alpha] at h
  have e : ((0 : P.F.Pt p).1) = (0 : Fin d → OC p) := rfl
  rw [e, ev_zeroPt] at h
  exact h

/-- `α(x)(y) ∈ 1 + m_{ℂ_p}`. -/
theorem norm_alpha_sub_one_lt (x : P.F.Pt p) (y : P.pdivGroup.DualTate S) :
    ‖((P.alpha hpm x y - 1 : OC p) : ℂ_[p])‖ < 1 := by
  have h0 : constantCoeff (P.charSeries hpm y - 1) = 0 := by
    rw [map_sub, constantCoeff_charSeries, map_one, sub_self]
  have := FGL.norm_ev_lt h0 x.2
  rwa [← evS_apply, map_sub, map_one, evS_apply] at this

end PDivFGL

end PadicHodge
