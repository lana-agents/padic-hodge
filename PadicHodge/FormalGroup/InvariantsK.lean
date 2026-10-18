/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.FormalGroup.Invariants
import PadicHodge.Cyclotomic.Norms

/-!
# Galois invariants of `F(m_{ℂ_p})` over a finite extension `K'/ℚ_p`

Versions of `FormalGroup/Invariants.lean` over a finite extension `L = K'` of `ℚ_p` inside
`ℚ̄_p` (an `IntermediateField ℚ_[p] (PadicAlgCl p)` with `[FiniteDimensional ℚ_[p] L]`), as
needed to run `AlphaInj.lean` with base `O_{K'}`:

* `exists_norm_le_of_mem_cpSubmodule`: **discreteness**: there is `r < 1` with `|x| ≤ r` for
  all `x ∈ L` with `|x| < 1` (`|x|^{[L:ℚ_p]} ∈ p^ℤ`, `norm_pow_finrank_eq_zpow`); this is the
  bound `|π_L|` of the proof of [Hong, Lemma 3.4.3];
* `FGL.eq_zero_of_forall_pow_nsmul_mem`: **[Hong, Lemma 3.4.3] over `L`**:
  `⋂_n p^n F(m_L) = 0`;
* `FGL.coord_mem_of_fixed`: **[Hong, Lemma 3.4.2] over `L`**: the coordinates of a
  `Gal(ℚ̄_p/L)`-invariant point lie in `L` (from `galPt_fixed_iff`);
* the Galois action of a single `σ` fixing the coefficients of `F` (`CoeffFixed`; e.g. all
  `σ ∈ G_L` if the coefficients lie in `L`, `GalFixedOver`, `galFixedOver_of_mem`): `ev_autCp_of`,
  `galPt_add_of`, `galPt_nsmul_of`, `logF_galPt_of` (versions of the lemmas of
  `FormalGroup/GaloisAction.lean`, which assume `GalFixed`, i.e. all of `Γ_{ℚ_p}`).

## References

* [Hong] S. Hong, *Notes on p-adic Hodge theory*, Lemma 3.4.2, Lemma 3.4.3.
-/

noncomputable section

open MvPowerSeries Topology Filter Module

namespace PadicHodge

variable {p : ℕ} [hp : Fact p.Prime]

/-- **Discreteness of the absolute value on a finite extension `L/ℚ_p`**: there is `r < 1`
such that every `x ∈ L` with `|x| < 1` has `|x| ≤ r` (one can take `r = p^{-1/[L:ℚ_p]}`). -/
theorem exists_norm_le_of_mem_cpSubmodule (L : IntermediateField ℚ_[p] (PadicAlgCl p))
    [FiniteDimensional ℚ_[p] L] :
    ∃ r : ℝ, 0 ≤ r ∧ r < 1 ∧ ∀ z ∈ cpSubmodule L, ‖z‖ < 1 → ‖z‖ ≤ r := by
  set D := finrank ℚ_[p] L with hD
  have hD0 : 0 < D := Module.finrank_pos
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  have hpi0 : (0 : ℝ) ≤ (p : ℝ)⁻¹ := by positivity
  have hpi1 : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hp1
  refine ⟨(p : ℝ)⁻¹ ^ ((D : ℝ)⁻¹), Real.rpow_nonneg hpi0 _,
    Real.rpow_lt_one hpi0 hpi1 (by positivity), fun z hz hz1 => ?_⟩
  obtain ⟨a, ha, rfl⟩ := mem_cpSubmodule.mp hz
  rw [PadicComplex.norm_extends] at hz1 ⊢
  by_cases ha0 : a = 0
  · rw [ha0, norm_zero]
    exact Real.rpow_nonneg hpi0 _
  obtain ⟨v, hv⟩ := norm_pow_finrank_eq_zpow L ⟨a, ha⟩ fun h => ha0 (congrArg Subtype.val h)
  have hv' : ‖a‖ ^ D = (p : ℝ) ^ v := hv
  have hlt : (p : ℝ) ^ v < 1 := hv' ▸ pow_lt_one₀ (norm_nonneg _) hz1 hD0.ne'
  have hv0 : v ≤ -1 := by
    by_contra h
    exact absurd (one_le_zpow₀ hp1.le (by omega)) (not_le.mpr hlt)
  have hle : ‖a‖ ^ D ≤ (p : ℝ)⁻¹ := by
    rw [hv', ← zpow_neg_one]
    exact zpow_le_zpow_right₀ hp1.le hv0
  calc ‖a‖ = (‖a‖ ^ D) ^ ((D : ℝ)⁻¹) :=
        (Real.pow_rpow_inv_natCast (norm_nonneg _) hD0.ne').symm
    _ ≤ (p : ℝ)⁻¹ ^ ((D : ℝ)⁻¹) :=
        Real.rpow_le_rpow (pow_nonneg (norm_nonneg _) _) hle (by positivity)

namespace FGL

variable {R : Type*} [CommRing R] [UniformSpace R] [DiscreteUniformity R] [Algebra R (OC p)]
  {d : ℕ} (F : FGL R d)

/-- **[Hong, Lemma 3.4.3] over a finite extension `L/ℚ_p`**: `⋂_n p^n F(m_L) = 0`, i.e. a point
which is `p^n · y_n` for all `n`, with the coordinates of all `y_n` in `L`, is `0`. -/
theorem eq_zero_of_forall_pow_nsmul_mem (L : IntermediateField ℚ_[p] (PadicAlgCl p))
    [FiniteDimensional ℚ_[p] L] {x : F.Pt p}
    (h : ∀ n, ∃ y : F.Pt p, (∀ j, ((y.1 j : OC p) : ℂ_[p]) ∈ cpSubmodule L) ∧
      (p ^ n) • y = x) : x = 0 := by
  obtain ⟨r, hr0, hr1, hr⟩ := exists_norm_le_of_mem_cpSubmodule L
  refine F.eq_zero_of_forall_pow_nsmul hr0 hr1 fun n => ?_
  obtain ⟨y, hy, hyx⟩ := h n
  exact ⟨y, fun j => hr _ (hy j) (y.2 j), hyx⟩

omit [UniformSpace R] [DiscreteUniformity R] [Algebra R (OC p)] in
/-- **[Hong, Lemma 3.4.2] over a finite extension `L/ℚ_p`**: the coordinates of a
`Gal(ℚ̄_p/L)`-invariant point of `F(m_{ℂ_p})` lie in `L`. -/
theorem coord_mem_of_fixed (L : IntermediateField ℚ_[p] (PadicAlgCl p))
    [FiniteDimensional ℚ_[p] L] {x : F.Pt p}
    (hx : ∀ σ : PadicAlgCl p ≃ₐ[L] PadicAlgCl p,
      galPt (AlgEquiv.restrictScalarsHom ℚ_[p] σ) x = x) (j : Fin d) :
    ((x.1 j : OC p) : ℂ_[p]) ∈ cpSubmodule L :=
  (F.galPt_fixed_iff L x).mp hx j

omit [UniformSpace R] [DiscreteUniformity R] [Algebra R (OC p)] in
/-- [Hong, Lemma 3.4.2] over `L`, in the shape of `coord_mem_Qp_of_fixed`. -/
theorem exists_coord_eq_of_fixed (L : IntermediateField ℚ_[p] (PadicAlgCl p))
    [FiniteDimensional ℚ_[p] L] {x : F.Pt p}
    (hx : ∀ σ : PadicAlgCl p ≃ₐ[L] PadicAlgCl p,
      galPt (AlgEquiv.restrictScalarsHom ℚ_[p] σ) x = x) (j : Fin d) :
    ∃ a : L, ((x.1 j : OC p) : ℂ_[p]) = ((a : PadicAlgCl p) : ℂ_[p]) := by
  obtain ⟨a, ha, hac⟩ := mem_cpSubmodule.mp (F.coord_mem_of_fixed L hx j)
  exact ⟨⟨a, ha⟩, hac.symm⟩

/-! ### The action of a single `σ` fixing the coefficients -/

variable (p R) in
/-- The coefficients `R → O_{ℂ_p}` are fixed by `σ`. -/
def CoeffFixed (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) : Prop :=
  ∀ r : R, autCp σ ((algebraMap R (OC p) r : OC p) : ℂ_[p]) = algebraMap R (OC p) r

variable (p R) in
/-- The coefficients `R → O_{ℂ_p}` are fixed by `G_L = Gal(ℚ̄_p/L)`. -/
def GalFixedOver (L : IntermediateField ℚ_[p] (PadicAlgCl p)) : Prop :=
  ∀ σ : PadicAlgCl p ≃ₐ[L] PadicAlgCl p, CoeffFixed p R (AlgEquiv.restrictScalarsHom ℚ_[p] σ)

omit [UniformSpace R] [DiscreteUniformity R] in
theorem galFixedOver_of_galFixed (h : GalFixed p R) (L : IntermediateField ℚ_[p] (PadicAlgCl p)) :
    GalFixedOver p R L :=
  fun _ => h _

omit [UniformSpace R] [DiscreteUniformity R] in
/-- Coefficients in a finite extension `L/ℚ_p` are fixed by `G_L` (e.g. `R = O_L`). -/
theorem galFixedOver_of_mem (L : IntermediateField ℚ_[p] (PadicAlgCl p))
    [FiniteDimensional ℚ_[p] L]
    (h : ∀ r : R, ((algebraMap R (OC p) r : OC p) : ℂ_[p]) ∈ cpSubmodule L) :
    GalFixedOver p R L :=
  fun σ r => (galCp_eq_self_iff_mem (L := L) _).mpr (h r) σ

variable {F}

/-- **Evaluation commutes with `σ`** if `σ` fixes the coefficients. -/
theorem ev_autCp_of {σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p} (hσ : CoeffFixed p R σ)
    {σ' : Type*} [Finite σ'] (f : MvPowerSeries σ' R) {a : σ' → OC p}
    (ha : ∀ s, ‖((a s : OC p) : ℂ_[p])‖ < 1) :
    autCp σ ((ev p f a : OC p) : ℂ_[p]) = ev p f (fun s => autOC σ (a s)) := by
  have hσ' : ∀ r : R, autCp σ ((algebraMap R (OC p) r : OC p) : ℂ_[p]) =
      algebraMap R (OC p) r := hσ
  have ha' : ∀ s, ‖((autOC σ (a s) : OC p) : ℂ_[p])‖ < 1 := fun s => by
    rw [autOC_coe, norm_autCp]; exact ha s
  have h1 := ((hasSum_eval₂ continuous_algebraMap_OC (hasEval_of_norm_lt_one ha) f).map
    (OC p).subtype.toAddMonoidHom continuous_subtype_val).map (autCp σ).toAddMonoidHom
    (continuous_autCp σ)
  have h2 := (hasSum_eval₂ continuous_algebraMap_OC (hasEval_of_norm_lt_one ha') f).map
    (OC p).subtype.toAddMonoidHom continuous_subtype_val
  refine h1.unique (h2.congr_fun fun m => ?_)
  simp only [Function.comp_apply, RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe,
    Subring.coe_subtype, Subring.coe_mul, map_mul, coe_finsuppProd_OC, map_prod, map_pow,
    autOC_coe]
  simp only [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, hσ']

theorem galPt_add_of {σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p} (hσ : CoeffFixed p R σ)
    (x y : F.Pt p) : galPt σ (x + y) = galPt σ x + galPt σ y := by
  refine F.pt_ext fun i => Subtype.ext ?_
  rw [galPt_val, add_val, add_val, ev_autCp_of hσ _ (norm_pairPt_lt x.2 y.2)]
  congr 2
  funext v
  unfold pairPt
  split_ifs <;> rfl

theorem galPt_nsmul_of {σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p} (hσ : CoeffFixed p R σ)
    (n : ℕ) (x : F.Pt p) : galPt σ (n • x) = n • galPt σ x := by
  induction n with
  | zero =>
    refine F.pt_ext fun i => Subtype.ext ?_
    rw [zero_nsmul, zero_nsmul, galPt_val, zero_val, ZeroMemClass.coe_zero, map_zero]
  | succ n ih => rw [succ_nsmul, succ_nsmul, galPt_add_of hσ, ih]

/-- **`log_F` is `σ`-equivariant** if `σ` fixes the coefficients. -/
theorem logF_galPt_of {σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p} (hσ : CoeffFixed p R σ)
    (x : F.Pt p) (i : Fin d) : F.logF (galPt σ x) i = autCp σ (F.logF x i) := by
  have hseq : ∀ n, F.logSeq (galPt σ x) i n = autCp σ (F.logSeq x i n) := fun n => by
    rw [logSeq, logSeq, ← galPt_nsmul_of hσ, galPt_val, map_div₀, map_pow, map_natCast]
  have h := ((continuous_autCp σ).tendsto _).comp (F.tendsto_logSeq x i)
  refine tendsto_nhds_unique (F.tendsto_logSeq (galPt σ x) i) ?_
  refine h.congr fun n => ?_
  rw [Function.comp_apply, hseq]

end FGL

end PadicHodge
