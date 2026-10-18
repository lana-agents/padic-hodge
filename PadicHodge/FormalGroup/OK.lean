/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.FormalGroup.AlphaInjK
import PadicHodge.FormalGroup.OCAdicPi

/-!
# `O_L` as a coefficient ring for formal points, `L/ℚ_p` finite

The analogue of `FormalGroup/Zp.lean` over a finite extension `L = K'` of `ℚ_p` inside `ℚ̄_p`
(`L : IntermediateField ℚ_[p] (PadicAlgCl p)` with `[FiniteDimensional ℚ_[p] L]`). The ring of
integers `O_L = L ∩ O_{ℂ_p}` is realised as a subring of `O_{ℂ_p}` (`OLSub`), and `OL L` is that
ring with the discrete uniformity. All hypotheses of `Alpha.lean`, `AlphaGal.lean` and
`AlphaInjK.lean` are discharged:

* `OL.isUnit_iff`, `OL.mem_maximalIdeal_iff`: `O_L` is local with `𝔪_L = {|x| < 1}`;
* `OL.uniformizer`, `OL.maximalIdeal_eq`: `𝔪_L = (π)` for a uniformiser `π` (discreteness:
  `|x|^{[L:ℚ_p]} ∈ p^ℤ`, `norm_pow_finrank_eq_zpow`);
* `OL.instIsAdicComplete`: `O_L` is `𝔪_L`-adically complete (`L` is closed in `ℂ_p`);
* `OL.isAdicComplete_OC`: `O_{ℂ_p}` is complete for `𝔪_L O_{ℂ_p} = (π)`;
* `OL.p_mem`: `p ∈ 𝔪_L`; `OL.norm_lt_one`: `𝔪_L ↦ m_{ℂ_p}`;
* `OL.galFixedOver`: the coefficients are fixed by `G_L = Gal(ℚ̄_p/L)`;
* `PDivFGL.alphaK` (bimultiplicative, `G_L`-equivariant, the two squares of [Hong, Prop. 3.4.9])
  and **`PDivFGL.eq_zero_of_alphaK_eq_one`**, **`PDivFGL.dalpha_injective_OL`**: injectivity of
  `α` on `G(O_L)` and of `dα` on `t_G(L)` for `p`-divisible formal group laws over `O_L`.

## References

* [Hong] S. Hong, *Notes on p-adic Hodge theory*, Prop. 3.4.9.
-/

noncomputable section

open IsLocalRing WithConv Topology Filter Module

namespace PadicHodge

variable {p : ℕ} [hp : Fact p.Prime]

/-- `O_L = L ∩ O_{ℂ_p}` as a subring of `O_{ℂ_p}`. -/
def OLSub (L : IntermediateField ℚ_[p] (PadicAlgCl p)) : Subring (OC p) where
  carrier := {x | (x : ℂ_[p]) ∈ cpSubmodule L}
  mul_mem' {x y} hx hy := by
    have hx' : (x : ℂ_[p]) ∈ cpSubmodule L := hx
    have hy' : (y : ℂ_[p]) ∈ cpSubmodule L := hy
    obtain ⟨a, ha, hax⟩ := mem_cpSubmodule.mp hx'
    obtain ⟨b, hb, hby⟩ := mem_cpSubmodule.mp hy'
    change ((x * y : OC p) : ℂ_[p]) ∈ cpSubmodule L
    rw [Subring.coe_mul, ← hax, ← hby]
    have h := coe_mem_cpSubmodule (L := L) (mul_mem ha hb)
    simp only [PadicComplex.coe_eq, map_mul] at h ⊢
    exact h
  one_mem' := by
    change ((1 : OC p) : ℂ_[p]) ∈ cpSubmodule L
    have h := coe_mem_cpSubmodule (L := L) (one_mem L)
    simp only [PadicComplex.coe_eq, map_one] at h
    rwa [OneMemClass.coe_one]
  add_mem' {x y} hx hy := by
    have hx' : (x : ℂ_[p]) ∈ cpSubmodule L := hx
    have hy' : (y : ℂ_[p]) ∈ cpSubmodule L := hy
    change ((x + y : OC p) : ℂ_[p]) ∈ cpSubmodule L
    rw [Subring.coe_add]
    exact add_mem hx' hy'
  zero_mem' := by
    change ((0 : OC p) : ℂ_[p]) ∈ cpSubmodule L
    rw [ZeroMemClass.coe_zero]
    exact zero_mem _
  neg_mem' {x} hx := by
    have hx' : (x : ℂ_[p]) ∈ cpSubmodule L := hx
    change ((-x : OC p) : ℂ_[p]) ∈ cpSubmodule L
    rw [Subring.coe_neg]
    exact neg_mem hx'

/-- **The ring of integers `O_L`** of `L/ℚ_p`, with the discrete uniformity. -/
def OL (L : IntermediateField ℚ_[p] (PadicAlgCl p)) : Type := OLSub L

namespace OL

variable {L : IntermediateField ℚ_[p] (PadicAlgCl p)}

instance : CommRing (OL L) := inferInstanceAs (CommRing (OLSub L))

instance : UniformSpace (OL L) := ⊥

instance : DiscreteUniformity (OL L) := ⟨rfl⟩

/-- `O_L → O_{ℂ_p}`. -/
def toOC : OL L →+* OC p := (OLSub L).subtype

instance : Algebra (OL L) (OC p) := toOC.toAlgebra

theorem algebraMap_eq (x : OL L) : algebraMap (OL L) (OC p) x = toOC x := rfl

theorem toOC_injective : Function.Injective (toOC : OL L → OC p) :=
  fun _ _ h => Subtype.ext h

theorem mem (x : OL L) : ((toOC x : OC p) : ℂ_[p]) ∈ cpSubmodule L := (x : OLSub L).2

/-- The element of `O_L` given by `x ∈ O_{ℂ_p}` with `x ∈ L`. -/
def mk (x : OC p) (hx : (x : ℂ_[p]) ∈ cpSubmodule L) : OL L := (⟨x, hx⟩ : OLSub L)

theorem toOC_mk (x : OC p) (hx : (x : ℂ_[p]) ∈ cpSubmodule L) : toOC (mk x hx) = x := rfl

/-- The absolute value `|x|` of `x ∈ O_L`. -/
def nrm (x : OL L) : ℝ := ‖((toOC x : OC p) : ℂ_[p])‖

theorem nrm_nonneg (x : OL L) : 0 ≤ nrm x := norm_nonneg _

theorem nrm_le_one (x : OL L) : nrm x ≤ 1 := norm_OC_le _

theorem nrm_zero : nrm (0 : OL L) = 0 := by
  rw [nrm, map_zero, ZeroMemClass.coe_zero, norm_zero]

theorem nrm_one : nrm (1 : OL L) = 1 := by
  rw [nrm, map_one, OneMemClass.coe_one, norm_one]

theorem nrm_mul (x y : OL L) : nrm (x * y) = nrm x * nrm y := by
  rw [nrm, map_mul, Subring.coe_mul, norm_mul]; rfl

theorem nrm_pow (x : OL L) (n : ℕ) : nrm (x ^ n) = nrm x ^ n := by
  rw [nrm, map_pow, Subring.coe_pow, norm_pow]; rfl

theorem nrm_add_le (x y : OL L) : nrm (x + y) ≤ max (nrm x) (nrm y) := by
  rw [nrm, map_add, Subring.coe_add]
  exact IsUltrametricDist.norm_add_le_max _ _

theorem nrm_eq_zero_iff {x : OL L} : nrm x = 0 ↔ x = 0 := by
  refine ⟨fun h => toOC_injective (Subtype.ext ?_), fun h => h ▸ nrm_zero⟩
  rw [map_zero, ZeroMemClass.coe_zero]
  exact norm_eq_zero.mp h

theorem nrm_pos {x : OL L} (hx : x ≠ 0) : 0 < nrm x :=
  (nrm_nonneg x).lt_of_ne fun h => hx (nrm_eq_zero_iff.mp h.symm)

theorem nrm_natCast (n : ℕ) : nrm (n : OL L) = ‖(n : ℂ_[p])‖ := by
  rw [nrm, map_natCast]; rfl

instance : Nontrivial (OL L) :=
  ⟨⟨0, 1, fun h => zero_ne_one (by rw [← nrm_zero (L := L), ← nrm_one (L := L), h])⟩⟩

/-- **Division in `O_L`**: `|x| ≤ |y|`, `y ≠ 0` imply `y ∣ x`. -/
theorem dvd_of_nrm_le {x y : OL L} (hy : y ≠ 0) (h : nrm x ≤ nrm y) : y ∣ x := by
  have hy0 : ((toOC y : OC p) : ℂ_[p]) ≠ 0 := norm_pos_iff.mp (nrm_pos hy)
  obtain ⟨a, ha, hax⟩ := mem_cpSubmodule.mp (mem x)
  obtain ⟨b, hb, hby⟩ := mem_cpSubmodule.mp (mem y)
  have hc1 : ((toOC x : OC p) : ℂ_[p]) / ((toOC y : OC p) : ℂ_[p]) ∈ OC p := by
    rw [mem_OC, norm_div]; exact div_le_one_of_le₀ h (norm_nonneg _)
  have hcL : ((toOC x : OC p) : ℂ_[p]) / ((toOC y : OC p) : ℂ_[p]) ∈ cpSubmodule L := by
    refine mem_cpSubmodule.mpr ⟨a / b, div_mem ha hb, ?_⟩
    rw [← hax, ← hby]
    simp only [PadicComplex.coe_eq, map_div₀]
  refine ⟨mk ⟨_, hc1⟩ hcL, toOC_injective (Subtype.ext ?_)⟩
  rw [map_mul, Subring.coe_mul, toOC_mk]
  exact (mul_div_cancel₀ _ hy0).symm

theorem isUnit_iff {x : OL L} : IsUnit x ↔ nrm x = 1 := by
  constructor
  · rintro ⟨u, rfl⟩
    have h1 : nrm (u : OL L) * nrm ((u⁻¹ : (OL L)ˣ) : OL L) = 1 := by
      rw [← nrm_mul, Units.mul_inv, nrm_one]
    refine le_antisymm (nrm_le_one _) ?_
    calc (1 : ℝ) = nrm (u : OL L) * nrm ((u⁻¹ : (OL L)ˣ) : OL L) := h1.symm
      _ ≤ nrm (u : OL L) * 1 := mul_le_mul_of_nonneg_left (nrm_le_one _) (nrm_nonneg _)
      _ = nrm (u : OL L) := mul_one _
  · intro h
    have hx : x ≠ 0 := fun h0 => by rw [h0, nrm_zero] at h; exact zero_ne_one h
    obtain ⟨c, hc⟩ := dvd_of_nrm_le hx (nrm_one.trans h.symm).le
    exact ⟨⟨x, c, hc.symm, by rw [mul_comm]; exact hc.symm⟩, rfl⟩

theorem not_isUnit_iff {x : OL L} : ¬IsUnit x ↔ nrm x < 1 := by
  rw [isUnit_iff]
  exact ⟨fun h => (nrm_le_one x).lt_of_ne h, ne_of_lt⟩

instance : IsLocalRing (OL L) :=
  IsLocalRing.of_nonunits_add fun a b ha hb => by
    rw [mem_nonunits_iff, not_isUnit_iff] at ha hb ⊢
    exact (nrm_add_le a b).trans_lt (max_lt ha hb)

/-- **`𝔪_L = {|x| < 1}`**. -/
theorem mem_maximalIdeal_iff {x : OL L} : x ∈ maximalIdeal (OL L) ↔ nrm x < 1 := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_isUnit_iff]

/-! ### The uniformiser -/

variable [FiniteDimensional ℚ_[p] L]

/-- `|x|^{[L:ℚ_p]} ∈ p^ℤ` for `x ≠ 0`. -/
theorem exists_nrm_pow_eq {x : OL L} (hx : x ≠ 0) :
    ∃ v : ℤ, nrm x ^ finrank ℚ_[p] L = (p : ℝ) ^ v := by
  obtain ⟨a, ha, hax⟩ := mem_cpSubmodule.mp (mem x)
  have ha0 : (⟨a, ha⟩ : L) ≠ 0 := by
    intro h
    have h' : a = 0 := congrArg Subtype.val h
    apply hx
    apply toOC_injective
    apply Subtype.ext
    rw [map_zero, ZeroMemClass.coe_zero, ← hax, h', PadicComplex.coe_zero]
  obtain ⟨v, hv⟩ := norm_pow_finrank_eq_zpow L _ ha0
  refine ⟨v, ?_⟩
  rw [nrm, ← hax, PadicComplex.norm_extends]
  exact hv

variable (L) in
/-- **Existence of a uniformiser**: `π ≠ 0`, `|π| < 1`, and `|x| ≤ |π|` whenever `|x| < 1`. -/
theorem exists_uniformizer :
    ∃ π : OL L, π ≠ 0 ∧ nrm π < 1 ∧ ∀ x : OL L, nrm x < 1 → nrm x ≤ nrm π := by
  classical
  set D := finrank ℚ_[p] L with hD
  have hD0 : 0 < D := Module.finrank_pos
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  let P : ℤ → Prop := fun v => ∃ x : OL L, x ≠ 0 ∧ nrm x < 1 ∧ nrm x ^ D = (p : ℝ) ^ v
  have hbdd : ∃ b : ℤ, ∀ v, P v → v ≤ b := by
    refine ⟨-1, fun v ⟨x, _, hx1, hxv⟩ => ?_⟩
    have hlt : (p : ℝ) ^ v < 1 := hxv ▸ pow_lt_one₀ (nrm_nonneg x) hx1 hD0.ne'
    by_contra h
    exact absurd (one_le_zpow₀ hp1.le (by omega)) (not_le.mpr hlt)
  have hinh : ∃ v, P v := by
    have hp1' : nrm (p : OL L) < 1 := by rw [nrm_natCast]; exact FGL.np_lt_one
    have hp0 : (p : OL L) ≠ 0 := fun h0 => by
      have := nrm_natCast (L := L) p
      rw [h0, nrm_zero] at this
      exact (FGL.np_pos (p := p)).ne this
    obtain ⟨v, hv⟩ := exists_nrm_pow_eq hp0
    exact ⟨v, _, hp0, hp1', hv⟩
  obtain ⟨v0, ⟨π, hπ0, hπ1, hπv⟩, hmax⟩ := Int.exists_greatest_of_bdd hbdd hinh
  refine ⟨π, hπ0, hπ1, fun x hx => ?_⟩
  by_cases hx0 : x = 0
  · rw [hx0, nrm_zero]; exact nrm_nonneg π
  obtain ⟨w, hw⟩ := exists_nrm_pow_eq hx0
  have hwv := hmax w ⟨x, hx0, hx, hw⟩
  have h : nrm x ^ D ≤ nrm π ^ D := by
    rw [hw, hπv]; exact zpow_le_zpow_right₀ hp1.le hwv
  exact (pow_le_pow_iff_left₀ (nrm_nonneg x) (nrm_nonneg π) hD0.ne').mp h

variable (L) in
/-- A uniformiser `π` of `O_L`. -/
def uniformizer : OL L := (exists_uniformizer L).choose

theorem uniformizer_ne_zero : uniformizer L ≠ 0 := (exists_uniformizer L).choose_spec.1

theorem nrm_uniformizer_lt_one : nrm (uniformizer L) < 1 :=
  (exists_uniformizer L).choose_spec.2.1

theorem nrm_le_nrm_uniformizer {x : OL L} (hx : nrm x < 1) : nrm x ≤ nrm (uniformizer L) :=
  (exists_uniformizer L).choose_spec.2.2 x hx

/-- **`𝔪_L = (π)`**. -/
theorem maximalIdeal_eq : maximalIdeal (OL L) = Ideal.span {uniformizer L} := by
  ext x
  rw [mem_maximalIdeal_iff, Ideal.mem_span_singleton]
  constructor
  · intro hx
    exact dvd_of_nrm_le uniformizer_ne_zero (nrm_le_nrm_uniformizer hx)
  · rintro ⟨c, rfl⟩
    rw [nrm_mul]
    exact (mul_le_of_le_one_right (nrm_nonneg _) (nrm_le_one c)).trans_lt nrm_uniformizer_lt_one

/-- `x ∈ (π)^n` iff `|x| ≤ |π|^n`. -/
theorem mem_span_pow_iff (n : ℕ) (x : OL L) :
    x ∈ Ideal.span {uniformizer L} ^ n ↔ nrm x ≤ nrm (uniformizer L) ^ n := by
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  constructor
  · rintro ⟨c, rfl⟩
    rw [nrm_mul, nrm_pow]
    exact mul_le_of_le_one_right (pow_nonneg (nrm_nonneg _) _) (nrm_le_one c)
  · intro h
    have hπn : uniformizer L ^ n ≠ 0 := fun h0 => by
      have := nrm_pow (uniformizer L) n
      rw [h0, nrm_zero] at this
      exact (pow_pos (nrm_pos uniformizer_ne_zero) n).ne this
    rw [← nrm_pow] at h
    exact dvd_of_nrm_le hπn h

/-- **`O_L` is `𝔪_L`-adically complete.** -/
instance : IsAdicComplete (maximalIdeal (OL L)) (OL L) := by
  rw [maximalIdeal_eq]
  have hπ1 := nrm_uniformizer_lt_one (L := L)
  have ht : Tendsto (fun n : ℕ => nrm (uniformizer L) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (nrm_nonneg _) hπ1
  exact
  { haus' := fun x hx => by
      have h : ∀ n, nrm x ≤ nrm (uniformizer L) ^ n := fun n => by
        have := hx n
        rw [SModEq.zero, smul_eq_mul, Ideal.mul_top] at this
        exact (mem_span_pow_iff n x).mp this
      exact nrm_eq_zero_iff.mp
        (le_antisymm (ge_of_tendsto ht (Eventually.of_forall h)) (nrm_nonneg x))
    prec' := fun f hf => by
      set g : ℕ → ℂ_[p] := fun n => ((toOC (f n) : OC p) : ℂ_[p])
      have hd : ∀ {m n}, m ≤ n → ‖g n - g m‖ ≤ nrm (uniformizer L) ^ m := by
        intro m n hmn
        have := hf hmn
        rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at this
        have h2 := (mem_span_pow_iff m _).mp this
        rwa [nrm, map_sub, AddSubgroupClass.coe_sub, norm_sub_rev] at h2
      have hc : CauchySeq g := by
        rw [Metric.cauchySeq_iff']
        intro ε hε
        obtain ⟨N, hN⟩ := (ht.eventually (gt_mem_nhds hε)).exists_forall_of_atTop
        refine ⟨N, fun n hn => ?_⟩
        rw [dist_eq_norm]
        exact (hd hn).trans_lt (hN N le_rfl)
      obtain ⟨c, hcl⟩ := cauchySeq_tendsto_of_complete hc
      have hcO : c ∈ OC p :=
        isClosed_OC.mem_of_tendsto hcl (Eventually.of_forall fun n => (toOC (f n)).2)
      have hcL : c ∈ cpSubmodule L :=
        isClosed_cpSubmodule.mem_of_tendsto hcl (Eventually.of_forall fun n => mem (f n))
      refine ⟨mk ⟨c, hcO⟩ hcL, fun n => ?_⟩
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, mem_span_pow_iff, nrm, map_sub,
        AddSubgroupClass.coe_sub, toOC_mk]
      have hlim : Tendsto (fun k => ‖g n - g k‖) atTop (𝓝 ‖g n - c‖) :=
        (hcl.const_sub _).norm
      refine le_of_tendsto hlim ?_
      filter_upwards [eventually_ge_atTop n] with k hk
      rw [norm_sub_rev]
      exact hd hk }

omit [FiniteDimensional ℚ_[p] L] in
/-- `p ∈ 𝔪_L`. -/
theorem p_mem : (p : OL L) ∈ maximalIdeal (OL L) := by
  rw [mem_maximalIdeal_iff, nrm_natCast]; exact FGL.np_lt_one

omit [FiniteDimensional ℚ_[p] L] in
/-- `𝔪_L` maps into `m_{ℂ_p}`. -/
theorem norm_lt_one (r : OL L) (hr : r ∈ maximalIdeal (OL L)) :
    ‖((algebraMap (OL L) (OC p) r : OC p) : ℂ_[p])‖ < 1 :=
  mem_maximalIdeal_iff.mp hr

/-- **`O_{ℂ_p}` is complete for `𝔪_L O_{ℂ_p} = (π)`.** -/
instance isAdicComplete_OC :
    IsAdicComplete ((maximalIdeal (OL L)).map (algebraMap (OL L) (OC p))) (OC p) :=
  OC.isAdicComplete_of_map_eq_span (π := algebraMap (OL L) (OC p) (uniformizer L))
    (nrm_pos uniformizer_ne_zero) nrm_uniformizer_lt_one
    (by rw [maximalIdeal_eq, Ideal.map_span, Set.image_singleton])

omit [FiniteDimensional ℚ_[p] L] in
/-- The coefficients `O_L` lie in `L`. -/
theorem algebraMap_mem (r : OL L) :
    ((algebraMap (OL L) (OC p) r : OC p) : ℂ_[p]) ∈ cpSubmodule L :=
  mem r

/-- The coefficients `O_L` are fixed by `G_L = Gal(ℚ̄_p/L)`. -/
theorem galFixedOver : FGL.GalFixedOver p (OL L) L :=
  FGL.galFixedOver_of_mem L algebraMap_mem

end OL

namespace PDivFGL

variable {L : IntermediateField ℚ_[p] (PadicAlgCl p)} [FiniteDimensional ℚ_[p] L] {d : ℕ}
  (P : PDivFGL (OL L) d p)

/-- **`α : F(m_{ℂ_p}) × T_p(G^∨)(O_{ℂ_p}) → 1 + m_{ℂ_p}` over `O_L`** ([Hong, Prop. 3.4.9]). -/
def alphaK (x : P.F.Pt p) (y : P.pdivGroup.DualTate (OCd p)) : OC p :=
  P.alpha OL.p_mem x y

theorem alphaK_add (x x' : P.F.Pt p) (y : P.pdivGroup.DualTate (OCd p)) :
    P.alphaK (x + x') y = P.alphaK x y * P.alphaK x' y :=
  P.alpha_add OL.p_mem x x' y

theorem alphaK_mul (x : P.F.Pt p) (y y' : P.pdivGroup.DualTate (OCd p)) :
    P.alphaK x (y * y') = P.alphaK x y * P.alphaK x y' :=
  P.alpha_mul OL.p_mem x y y'

/-- `α` is `G_L`-equivariant. -/
theorem alphaK_gal (σ : PadicAlgCl p ≃ₐ[L] PadicAlgCl p) (x : P.F.Pt p)
    (y : P.pdivGroup.DualTate (OCd p)) :
    ((P.alphaK (FGL.galPt (AlgEquiv.restrictScalarsHom ℚ_[p] σ) x)
        (P.galDual (AlgEquiv.restrictScalarsHom ℚ_[p] σ) (OL.galFixedOver σ) y) : OC p) :
        ℂ_[p]) =
      autCp (AlgEquiv.restrictScalarsHom ℚ_[p] σ) ((P.alphaK x y : OC p) : ℂ_[p]) :=
  P.alpha_gal _ (OL.galFixedOver σ) OL.p_mem x y

/-- The left square of [Hong, Prop. 3.4.9] over `O_L`: on `p^v`-torsion, `α` is the Cartier
pairing. -/
theorem alphaK_torsion (v : ℕ) (x : P.F.torsionBy (p := p) v)
    (y : P.pdivGroup.DualTate (OCd p)) :
    P.alphaK x.1 y =
      (P.groupScheme v).pairing (OCd p) (toConv (toOCd (P.F.layerPt v x))) (y.1 v) :=
  P.alpha_torsion OL.p_mem v x y

/-- The right square of [Hong, Prop. 3.4.9] over `O_L`. -/
theorem logGm_alphaK (x : P.F.Pt p) (y : P.pdivGroup.DualTate (OCd p)) :
    (FGL.multiplicative (OCd p)).logF ((P.charHom OL.p_mem y).ptMap (P.toPtS x)) 0 =
      P.dalpha OL.p_mem (fun j => P.F.logF x j) y :=
  P.logGm_alpha OL.p_mem x y

/-- **`α` is injective on `G(O_L)`** ([Hong, Prop. 3.4.9], `K = L`): a `G_L`-invariant point
`x ∈ F(m_{ℂ_p})` with `α(x) = 1` is `0`. -/
theorem eq_zero_of_alphaK_eq_one (x : P.F.Pt p) (hx : ∀ y, P.alphaK x y = 1)
    (hfix : ∀ σ : PadicAlgCl p ≃ₐ[L] PadicAlgCl p,
      FGL.galPt (AlgEquiv.restrictScalarsHom ℚ_[p] σ) x = x) : x = 0 :=
  P.eq_zero_of_alpha_eq_one_K OL.p_mem OL.norm_lt_one L OL.galFixedOver x hx hfix

/-- **`dα` is injective on `t_G(L) = L^d`** ([Hong, Prop. 3.4.9], `K = L`). -/
theorem dalpha_injective_OL (z : Fin d → L)
    (h : ∀ y, P.dalpha OL.p_mem (fun j => (((z j : L) : PadicAlgCl p) : ℂ_[p])) y = 0) :
    z = 0 :=
  P.dalpha_injective_K OL.p_mem OL.norm_lt_one L OL.galFixedOver z h

end PDivFGL

end PadicHodge
