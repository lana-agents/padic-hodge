/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.FormalGroup.Zp
import PadicHodge.FormalGroup.Divisible
import PadicHodge.FormalGroup.Invariants
import PadicHodge.FormalGroup.LayerSurj
import PadicHodge.GroupScheme.DualTateOC

/-!
# Injectivity of `α` on `G(ℤ_p)` ([Hong, Prop. 3.4.9, proof])

For a `p`-divisible formal group law `P` over `R` (as in `Alpha.lean`; `R → O_{ℂ_p}` sends `𝔪_R`
into `m_{ℂ_p}`) with `G = F[p^∞]` and `α : F(m_{ℂ_p}) × T_p(G^∨)(O_{ℂ_p}) → 1 + m_{ℂ_p}`:

* `eq_zero_of_alpha_torsion`: **`α` is injective on torsion points**: for `x ∈ F[p^v]`,
  `α(x) = ⟨x_v, (·)_v⟩` (`alpha_torsion`), `T_p(G^∨)(O_{ℂ_p}) → G_v^∨(O_{ℂ_p})` is surjective
  (`DualTate.proj_surjective_OC`) and the Cartier pairing over `O_{ℂ_p}` separates points
  (`eq_one_of_pairing_OC`);
* `exists_torsion_alpha_eq`: if `α(x)^p = 1`, then `α(x) = α(t)` for some `t ∈ F[p]`: the character
  `α(x)` of `T_p(G^∨)` kills `p T_p(G^∨) = ker(T_p(G^∨) → G_1^∨)` (`DualTate.exists_pow_eq_OC`),
  so it factors through `G_1^∨(O_{ℂ_p})`, where it is `⟨t_1, ·⟩` by perfectness
  (`exists_pairing_eq_OC`), and `t_1` is the layer point of some `t ∈ F[p]`
  (`layerPt_surjective`);
* **`eq_zero_of_alpha_eq_one`** ([Hong, Prop. 3.4.9]: `α` is injective on `G(O_K)`, `K = ℚ_p`):
  a Galois-invariant point `x` with `α(x) = 1` is `0`. Route (avoiding the snake lemma used in
  [Hong]): if `z ∈ ker α` is invariant, write `z = p x''` (`exists_p_nsmul_eq`); then `α(x'')`
  is `p`-torsion, so `α(x'') = α(t)` with `t ∈ F[p]`, and `x' = x'' − t ∈ ker α` has
  `p x' = z`; for `σ ∈ Γ_{ℚ_p}`, `σx' − x' ∈ ker α ∩ F[p] = 0` (Galois equivariance
  `alpha_gal`), so `x'` is invariant. Hence `x` is `p^n`-divisible by invariant points for all
  `n`, whose coordinates lie in `ℚ_p` ([Hong, Lemma 3.4.2], `galPt_fixed_iff`), and `x = 0` by
  [Hong, Lemma 3.4.3] (`eq_zero_of_forall_pow_nsmul_Qp`).
-/

noncomputable section

open MvPowerSeries IsLocalRing WithConv

namespace PadicHodge

namespace FGL

variable {p : ℕ} [hp : Fact p.Prime] {R : Type*} [CommRing R] [UniformSpace R]
  [DiscreteUniformity R] [Algebra R (OC p)] {d : ℕ}

instance finiteDimensional_bot_Qp :
    FiniteDimensional ℚ_[p] (⊥ : IntermediateField ℚ_[p] (PadicAlgCl p)) :=
  Module.finite_of_finrank_eq_succ IntermediateField.finrank_bot

omit [UniformSpace R] [DiscreteUniformity R] [Algebra R (OC p)] in
/-- **[Hong, Lemma 3.4.2] over `ℚ_p`**: the coordinates of a `Gal(ℚ̄_p/ℚ_p)`-invariant point
of `F(m_{ℂ_p})` lie in `ℚ_p`. -/
theorem coord_mem_Qp_of_fixed (F : FGL R d) {x : F.Pt p} (hx : ∀ σ, galPt σ x = x) (j : Fin d) :
    ∃ q : ℚ_[p], ((x.1 j : OC p) : ℂ_[p]) = algebraMap ℚ_[p] ℂ_[p] q := by
  have h := (F.galPt_fixed_iff (⊥ : IntermediateField ℚ_[p] (PadicAlgCl p)) x).mp
    (fun σ => hx _) j
  obtain ⟨a, ha, hac⟩ := Submodule.mem_map.mp h
  obtain ⟨q, rfl⟩ := IntermediateField.mem_bot.mp ha
  refine ⟨q, ?_⟩
  rw [← hac]
  change algebraMap (PadicAlgCl p) ℂ_[p] (algebraMap ℚ_[p] (PadicAlgCl p) q) = _
  rw [← IsScalarTower.algebraMap_apply]

end FGL

namespace PDivFGL

open FFGroupScheme FGL

variable {p : ℕ} [hp : Fact p.Prime] {R : Type} [CommRing R] [IsLocalRing R]
  [IsAdicComplete (maximalIdeal R) R] [UniformSpace R] [DiscreteUniformity R] [Algebra R (OC p)]
  {d : ℕ} (P : PDivFGL R d p)
  [hC : IsAdicComplete ((maximalIdeal R).map (algebraMap R (OC p))) (OC p)]
  (hpm : (p : R) ∈ maximalIdeal R)

local notation "S" => OCd p

omit [UniformSpace R] [DiscreteUniformity R] in
theorem charSeries_one : P.charSeries hpm 1 = 1 :=
  (P.charSeries_unique hpm 1 1 fun v => by
    rw [map_one, charB]
    exact ((P.groupScheme v).charOf_one S).symm).symm

omit [UniformSpace R] [DiscreteUniformity R] in
theorem alpha_one (x : P.F.Pt p) : P.alpha hpm x 1 = 1 := by
  rw [alpha, charSeries_one, ← evS_apply, map_one]

/-- `α(x)` as a character of `T_p(G^∨)(O_{ℂ_p})`. -/
def alphaHom (x : P.F.Pt p) : P.pdivGroup.DualTate S →* OC p where
  toFun := P.alpha hpm x
  map_one' := P.alpha_one hpm x
  map_mul' := P.alpha_mul hpm x

theorem alpha_nsmul (n : ℕ) (x : P.F.Pt p) (y : P.pdivGroup.DualTate S) :
    P.alpha hpm (n • x) y = P.alpha hpm x y ^ n := by
  induction n with
  | zero => rw [zero_nsmul, pow_zero, alpha_zero]
  | succ n ih => rw [succ_nsmul, alpha_add, ih, pow_succ]

/-- The layer point `x_v ∈ G_v(O_{ℂ_p})` of `x ∈ F[p^v]`. -/
abbrev layerPoint (v : ℕ) (x : P.F.torsionBy (p := p) v) : (P.groupScheme v).points S :=
  toConv (toOCd (P.F.layerPt v x))

omit hC [UniformSpace R] [DiscreteUniformity R] in
theorem proj_surjective_OCd (v : ℕ) (ψ : (P.groupScheme v).dual.points S) :
    ∃ y : P.pdivGroup.DualTate S, y.1 v = ψ :=
  PDivGroup.DualTate.proj_surjective_OC P.pdivGroup v ψ

omit hC [UniformSpace R] [DiscreteUniformity R] in
theorem exists_pow_eq_OCd (y : P.pdivGroup.DualTate S) (hy : y.1 1 = 1) :
    ∃ w : P.pdivGroup.DualTate S, w ^ p = y :=
  PDivGroup.DualTate.exists_pow_eq_OC P.pdivGroup y hy

/-- A torsion point on which `α` is trivial has trivial layer point. -/
theorem layerPoint_eq_one (v : ℕ) (x : P.F.torsionBy (p := p) v)
    (h : ∀ y, P.alpha hpm x.1 y = 1) : P.layerPoint v x = 1 := by
  refine (P.groupScheme v).eq_one_of_pairing_OC (pow_ne_zero v hp.out.ne_zero)
    (P.pdivGroup.univPt_pow_eq_one v) _ fun ψ => ?_
  obtain ⟨y, hy⟩ := P.proj_surjective_OCd v ψ
  have := P.alpha_torsion hpm v x y
  rw [h y] at this
  rw [← hy]
  exact this.symm

/-- **`α` is injective on torsion points.** -/
theorem eq_zero_of_alpha_torsion (v : ℕ) (x : P.F.torsionBy (p := p) v)
    (h : ∀ y, P.alpha hpm x.1 y = 1) : x.1 = 0 := by
  have h0 := P.layerPoint_eq_one hpm v ⟨0, (P.F.torsionBy v).zero_mem⟩
    fun y => P.alpha_zero hpm y
  have h1 := P.layerPoint_eq_one hpm v x h
  have : P.F.layerPt v x = P.F.layerPt v ⟨0, (P.F.torsionBy v).zero_mem⟩ := by
    have := h1.trans h0.symm
    exact WithConv.toConv_injective this
  exact congrArg Subtype.val (P.F.layerPt_injective v this)

variable (hR : ∀ r ∈ maximalIdeal R, ‖(algebraMap R (OC p) r : ℂ_[p])‖ < 1)

include hR in
/-- **A `p`-torsion character `α(x)` is `α(t)` for some `t ∈ F[p]`.** -/
theorem exists_torsion_alpha_eq (x : P.F.Pt p) (hx : ∀ y, P.alpha hpm x y ^ p = 1) :
    ∃ t : P.F.torsionBy (p := p) 1, ∀ y, P.alpha hpm t.1 y = P.alpha hpm x y := by
  set χ := P.alphaHom hpm x
  let π : P.pdivGroup.DualTate S →* (P.groupScheme 1).dual.points S :=
    (Pi.evalMonoidHom (fun w => (P.groupScheme w).dual.points S) 1).comp
      (P.pdivGroup.DualTate S).subtype
  have hπ : Function.Surjective π := fun ψ => P.proj_surjective_OCd 1 ψ
  have hker : π.ker ≤ χ.ker := by
    intro y hy
    obtain ⟨w, rfl⟩ := P.exists_pow_eq_OCd y hy
    rw [MonoidHom.mem_ker, map_pow]
    exact hx w
  let e := QuotientGroup.quotientKerEquivOfSurjective π hπ
  let χ' : (P.groupScheme 1).dual.points S →* OC p :=
    (QuotientGroup.lift π.ker χ hker).comp e.symm.toMonoidHom
  have hχ' : ∀ y, χ' (π y) = χ y := by
    intro y
    have : e.symm (π y) = (y : _ ⧸ π.ker) := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    simp only [χ', MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, this]
    rfl
  obtain ⟨t1, ht1⟩ := (P.groupScheme 1).exists_pairing_eq_OC (p := p) (pow_ne_zero 1 hp.out.ne_zero)
    (P.pdivGroup.univPt_pow_eq_one 1) (P.pdivGroup.card_points_Cp 1) χ'
  obtain ⟨t, ht⟩ := P.layerPt_surjective hR 1 (ofConv t1)
  have ht' : toConv (P.F.layerPt 1 t) = t1 := by rw [ht, toConv_ofConv]
  subst ht'
  refine ⟨t, fun y => ?_⟩
  rw [P.alpha_torsion hpm 1 t y]
  change (P.groupScheme 1).pairing (OC p) (toConv (P.F.layerPt 1 t)) (y.1 1) = P.alpha hpm x y
  rw [ht1 (y.1 1)]
  exact hχ' y

/-! ### Galois-invariant points -/

omit hC [UniformSpace R] [DiscreteUniformity R] in
/-- `σ` acts bijectively on `T_p(G^∨)(O_{ℂ_p})`: `σ (σ⁻¹ y) = y`. -/
theorem galDual_galDual_inv (hRG : GalFixed p R) (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)
    (y : P.pdivGroup.DualTate S) :
    P.galDual σ (hRG σ) (P.galDual σ⁻¹ (hRG σ⁻¹) y) = y := by
  apply Subtype.ext
  funext v
  apply WithConv.ofConv_injective
  ext a
  apply Subtype.ext
  change autCp σ (autCp σ⁻¹ ((OCd.toOC (ofConv (y.1 v) a) : OC p) : ℂ_[p])) =
    ((OCd.toOC (ofConv (y.1 v) a) : OC p) : ℂ_[p])
  rw [autCp_apply, autCp_apply, ← autCpHom_mul, mul_inv_cancel, autCpHom_one]

include hR in
/-- **Divisibility step**: an invariant `z ∈ ker α` is `p x'` with `x'` invariant, `x' ∈ ker α`. -/
theorem exists_p_nsmul_eq_of_alpha (hRG : GalFixed p R) (z : P.F.Pt p)
    (hz : ∀ y, P.alpha hpm z y = 1) (hfix : ∀ σ, galPt σ z = z) :
    ∃ x' : P.F.Pt p, (∀ y, P.alpha hpm x' y = 1) ∧ (∀ σ, galPt σ x' = x') ∧ p • x' = z := by
  obtain ⟨x'', hx''⟩ := P.exists_p_nsmul_eq hR z
  have hp' : ∀ y, P.alpha hpm x'' y ^ p = 1 := fun y => by
    rw [← alpha_nsmul, hx'', hz]
  obtain ⟨t, ht⟩ := P.exists_torsion_alpha_eq hpm hR x'' hp'
  have hunit : ∀ y, IsUnit (P.alpha hpm t.1 y) := fun y =>
    P.isUnit_alpha_torsion hpm 1 t y
  set x' := x'' - t.1
  have hx' : ∀ y, P.alpha hpm x' y = 1 := fun y => by
    have h := P.alpha_add hpm x' t.1 y
    rw [sub_add_cancel, ← ht y] at h
    exact (hunit y).mul_left_cancel (by rw [mul_one, mul_comm]; exact h.symm.trans (by ring))
  have hpx' : p • x' = z := by
    have ht0 : p • t.1 = 0 := by
      have := t.2
      rwa [FGL.mem_torsionBy, pow_one] at this
    rw [nsmul_sub, ht0, sub_zero, hx'']
  refine ⟨x', hx', fun σ => ?_, hpx'⟩
  -- `u = σx' − x'` is `p`-torsion and in `ker α`
  set u := galPt σ x' - x'
  have hu : u ∈ P.F.torsionBy (p := p) 1 := by
    rw [FGL.mem_torsionBy, pow_one, nsmul_sub, ← galPt_nsmul hRG, hpx', hfix σ, sub_self]
  have hneg : ∀ y, P.alpha hpm (-x') y = 1 := fun y => by
    have h := P.alpha_add hpm x' (-x') y
    rw [add_neg_cancel, alpha_zero, hx', one_mul] at h
    exact h.symm
  have hσ : ∀ y, P.alpha hpm (galPt σ x') y = 1 := fun y => by
    rw [← P.galDual_galDual_inv hRG σ y]
    apply Subtype.ext
    rw [P.alpha_gal σ (hRG σ) hpm, hx']
    simp
  have hu0 := P.eq_zero_of_alpha_torsion hpm 1 ⟨u, hu⟩ fun y => by
    change P.alpha hpm (galPt σ x' + -x') y = 1
    rw [alpha_add, hσ, hneg, one_mul]
  exact sub_eq_zero.mp hu0

include hR in
/-- **`α` is injective on `G(ℤ_p)`** ([Hong, Prop. 3.4.9, proof], `K = ℚ_p`): a point of
`F(m_{ℂ_p})` fixed by `Gal(ℚ̄_p/ℚ_p)` with `α(x) = 1` is `0`. -/
theorem eq_zero_of_alpha_eq_one (hRG : GalFixed p R) (x : P.F.Pt p)
    (hx : ∀ y, P.alpha hpm x y = 1) (hfix : ∀ σ, galPt σ x = x) : x = 0 := by
  have key : ∀ n : ℕ, ∃ z : P.F.Pt p, (∀ y, P.alpha hpm z y = 1) ∧ (∀ σ, galPt σ z = z) ∧
      (p ^ n) • z = x := by
    intro n
    induction n with
    | zero => exact ⟨x, hx, hfix, by rw [pow_zero, one_nsmul]⟩
    | succ n ih =>
      obtain ⟨z, hz, hzfix, hzx⟩ := ih
      obtain ⟨z', hz', hz'fix, hz'z⟩ := P.exists_p_nsmul_eq_of_alpha hpm hR hRG z hz hzfix
      exact ⟨z', hz', hz'fix, by rw [pow_succ', mul_nsmul, hz'z, hzx]⟩
  refine P.F.eq_zero_of_forall_pow_nsmul_Qp fun n => ?_
  obtain ⟨z, -, hzfix, hzx⟩ := key n
  refine ⟨z, fun j => ?_, hzx⟩
  exact coord_mem_Qp_of_fixed P.F hzfix j

end PDivFGL

end PadicHodge
