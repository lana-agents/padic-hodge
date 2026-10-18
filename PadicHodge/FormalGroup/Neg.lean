/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.FormalGroup.Log
import Mathlib.Topology.MetricSpace.Contracting

/-!
# Inverses: `F(m_{ℂ_p})` is a group

For a formal group law `F` of dimension `d` (setting of `FormalGroup/Points.lean`) every point
`x` of the open polydisc has an inverse `y` with `Φ(x, y) = 0` ([Hong, Lemma 2.2.5 (3)] gives the
formal inverse `ι(T)`; we construct the inverse point directly). The argument is analytic:

* `norm_prod_sub_prod_le`, `norm_monomial_sub_le'`: ultrametric estimates for differences of
  monomials;
* `norm_add_sub_add_le`, `norm_add_sub_add_le'`: `Φ` is `1`-Lipschitz up to an error
  `r δ` in each variable: `|Φ(x, y) − Φ(x', y) − (x − x')| ≤ r δ` if `|y| ≤ r`,
  `|x − x'| ≤ δ` (the monomials of `Φ_i` not involving `U` give `Φ_i(x, 0) = x_i`, the others
  carry a factor `y_j`);
* `exists_fixed_of_contract`: Banach's fixed point theorem on a closed polydisc of `ℂ_p^d`;
* `exists_neg`: `y ↦ y − Φ(x, y)` contracts the polydisc of radius `r = max |x_j|` with
  constant `r`, its fixed point is the inverse; `instAddCommGroupPt`, and `bnd_neg`: `−x` lies
  in every polydisc of radius `< 1` containing `x`.
* `rad`: the radius `max_j |x_j|` of a point.
-/

noncomputable section

open MvPowerSeries Topology Filter Function Set

namespace PadicHodge

variable {p : ℕ} [hp : Fact p.Prime]

theorem norm_sub_le_max_Cp (a b : ℂ_[p]) : ‖a - b‖ ≤ max ‖a‖ ‖b‖ := by
  rw [sub_eq_add_neg]
  simpa using IsUltrametricDist.norm_add_le_max a (-b)

/-- **Ultrametric estimate for differences of products** of elements of the unit ball. -/
theorem norm_prod_sub_prod_le {ι : Type*} (s : Finset ι) {u v : ι → ℂ_[p]} {δ : ℝ}
    (hδ : 0 ≤ δ) (hu : ∀ i ∈ s, ‖u i‖ ≤ 1) (hv : ∀ i ∈ s, ‖v i‖ ≤ 1)
    (huv : ∀ i ∈ s, ‖u i - v i‖ ≤ δ) :
    ‖∏ i ∈ s, u i - ∏ i ∈ s, v i‖ ≤ δ := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hδ
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    have e : u a * ∏ i ∈ s, u i - v a * ∏ i ∈ s, v i =
        u a * (∏ i ∈ s, u i - ∏ i ∈ s, v i) + (u a - v a) * ∏ i ∈ s, v i := by ring
    rw [e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · rw [norm_mul]
      calc ‖u a‖ * ‖∏ i ∈ s, u i - ∏ i ∈ s, v i‖ ≤ 1 * δ :=
            mul_le_mul (hu a (Finset.mem_insert_self _ _))
              (ih (fun i hi => hu i (Finset.mem_insert_of_mem hi))
                (fun i hi => hv i (Finset.mem_insert_of_mem hi))
                (fun i hi => huv i (Finset.mem_insert_of_mem hi))) (norm_nonneg _) zero_le_one
        _ = δ := one_mul δ
    · rw [norm_mul, norm_prod]
      calc ‖u a - v a‖ * ∏ i ∈ s, ‖v i‖ ≤ δ * 1 :=
            mul_le_mul (huv a (Finset.mem_insert_self _ _))
              (Finset.prod_le_one (fun i _ => norm_nonneg _)
                fun i hi => hv i (Finset.mem_insert_of_mem hi)) (by positivity) hδ
        _ = δ := mul_one δ

theorem norm_pow_sub_pow_le_of_le_one {a b : ℂ_[p]} {δ : ℝ} (hδ : 0 ≤ δ)
    (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1)
    (hab : ‖a - b‖ ≤ δ) (e : ℕ) : ‖a ^ e - b ^ e‖ ≤ δ := by
  have h := norm_prod_sub_prod_le (Finset.range e) (u := fun _ => a) (v := fun _ => b) hδ
    (fun _ _ => ha) (fun _ _ => hb) (fun _ _ => hab)
  simpa only [Finset.prod_const, Finset.card_range] using h

theorem coe_finsuppProd_OC {σ : Type*} (a : σ → OC p) (m : σ →₀ ℕ) :
    (((m.prod fun s e => a s ^ e) : OC p) : ℂ_[p]) =
      ∏ s ∈ m.support, ((a s : OC p) : ℂ_[p]) ^ m s := by
  have : (((m.prod fun s e => a s ^ e) : OC p) : ℂ_[p]) =
      (OC p).subtype (m.prod fun s e => a s ^ e) := rfl
  rw [this, map_finsuppProd, Finsupp.prod]
  rfl

/-- **Difference of monomials sharing a small variable**: if `a_{s₁} = b_{s₁}`, `|a_{s₁}| ≤ r`
and `s₁` occurs in `m`, then `|a^m − b^m| ≤ r δ`. -/
theorem norm_monomial_sub_le' {σ : Type*} {a b : σ → OC p} {r δ : ℝ} (hr0 : 0 ≤ r)
    (hr1 : r ≤ 1) (hδ : 0 ≤ δ) (hab : ∀ s, ‖((a s : OC p) : ℂ_[p]) - b s‖ ≤ δ)
    (m : σ →₀ ℕ) {s₁ : σ} (hs₁ : s₁ ∈ m.support) (he : a s₁ = b s₁)
    (har : ‖((a s₁ : OC p) : ℂ_[p])‖ ≤ r) :
    ‖(((m.prod fun s e => a s ^ e) : OC p) : ℂ_[p]) -
      (((m.prod fun s e => b s ^ e) : OC p) : ℂ_[p])‖ ≤ r * δ := by
  classical
  rw [coe_finsuppProd_OC, coe_finsuppProd_OC, ← Finset.mul_prod_erase _ _ hs₁,
    ← Finset.mul_prod_erase _ _ hs₁, he, ← mul_sub, norm_mul]
  have hm : m s₁ ≠ 0 := Finsupp.mem_support_iff.mp hs₁
  refine mul_le_mul ?_ ?_ (norm_nonneg _) hr0
  · rw [norm_pow, ← he]
    calc ‖((a s₁ : OC p) : ℂ_[p])‖ ^ m s₁ ≤ ‖((a s₁ : OC p) : ℂ_[p])‖ ^ 1 :=
          pow_le_pow_of_le_one (norm_nonneg _) (har.trans hr1) (Nat.one_le_iff_ne_zero.mpr hm)
      _ ≤ r := by rw [pow_one]; exact har
  · refine norm_prod_sub_prod_le _ hδ (fun s _ => ?_) (fun s _ => ?_) fun s _ =>
      norm_pow_sub_pow_le_of_le_one hδ (norm_OC_le _) (norm_OC_le _) (hab s) _
    · rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) (norm_OC_le _)
    · rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) (norm_OC_le _)

/-- **Banach's fixed point theorem on a closed polydisc of `ℂ_p^d`.** -/
theorem exists_fixed_of_contract {d : ℕ} (S : (Fin d → ℂ_[p]) → Fin d → ℂ_[p]) {r c : ℝ}
    (hr : 0 ≤ r) (hc0 : 0 ≤ c) (hc1 : c < 1)
    (hmaps : ∀ v : Fin d → ℂ_[p], (∀ j, ‖v j‖ ≤ r) → ∀ j, ‖S v j‖ ≤ r)
    (hcon : ∀ v w : Fin d → ℂ_[p], (∀ j, ‖v j‖ ≤ r) → (∀ j, ‖w j‖ ≤ r) → ∀ δ : ℝ, 0 ≤ δ →
      (∀ j, ‖v j - w j‖ ≤ δ) → ∀ j, ‖S v j - S w j‖ ≤ c * δ) :
    ∃ v : Fin d → ℂ_[p], (∀ j, ‖v j‖ ≤ r) ∧ S v = v := by
  set s : Set (Fin d → ℂ_[p]) := {v | ∀ j, ‖v j‖ ≤ r}
  have hs : IsClosed s := by
    have : s = ⋂ j, {v : Fin d → ℂ_[p] | ‖v j‖ ≤ r} := by ext v; simp [s]
    rw [this]
    exact isClosed_iInter fun j =>
      isClosed_le (continuous_norm.comp (continuous_apply j)) continuous_const
  have hmapsTo : MapsTo S s s := fun v hv => hmaps v hv
  have hK : ContractingWith (Real.toNNReal c) (hmapsTo.restrict S s s) := by
    refine ⟨by rw [Real.toNNReal_lt_one]; exact hc1, LipschitzWith.of_dist_le_mul fun a b => ?_⟩
    rw [Real.coe_toNNReal _ hc0, Subtype.dist_eq, Subtype.dist_eq]
    refine (dist_pi_le_iff (mul_nonneg hc0 dist_nonneg)).mpr fun j => ?_
    rw [dist_eq_norm]
    refine hcon a.1 b.1 a.2 b.2 _ dist_nonneg (fun k => ?_) j
    rw [← dist_eq_norm]
    exact dist_le_pi_dist a.1 b.1 k
  obtain ⟨v, hv, hfix, -⟩ := ContractingWith.exists_fixedPoint' hs.isComplete hmapsTo hK
    (x := 0) (fun j => by simpa using hr) (edist_ne_top _ _)
  exact ⟨v, hv, hfix⟩

namespace FGL

variable {R : Type*} [CommRing R] [UniformSpace R] [DiscreteUniformity R] [Algebra R (OC p)]
  {d : ℕ} (F : FGL R d)

/-- **`Φ` is `1`-Lipschitz in the first variable up to `r δ`.** -/
theorem norm_add_sub_add_le {x x' y : F.Pt p} {r δ : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hδ : 0 ≤ δ) (hy : F.Bnd y r) (hxx : ∀ j, ‖((x.1 j : OC p) : ℂ_[p]) - x'.1 j‖ ≤ δ)
    (i : Fin d) :
    ‖(((x + y).1 i : OC p) : ℂ_[p]) - (x' + y).1 i - (x.1 i - x'.1 i)‖ ≤ r * δ := by
  classical
  set f := F.Φ i
  set φ := algebraMap R (OC p)
  let a : Fin 2 × Fin d → OC p := pairPt x.1 y.1
  let a' : Fin 2 × Fin d → OC p := pairPt x'.1 y.1
  let χ0 : Fin 2 × Fin d → OC p := fun s => if s ∈ {s : Fin 2 × Fin d | s.1 = 0} then 1 else 0
  have ha0 : pairPt x.1 (0 : Fin d → OC p) = a * χ0 := by
    funext ⟨c, j⟩
    fin_cases c <;> simp [a, χ0, pairPt]
  have ha0' : pairPt x'.1 (0 : Fin d → OC p) = a' * χ0 := by
    funext ⟨c, j⟩
    fin_cases c <;> simp [a', χ0, pairPt]
  have hev : ∀ b : Fin 2 × Fin d → OC p, (∀ s, ‖((b s : OC p) : ℂ_[p])‖ < 1) →
      HasSum (fun m => (((φ (coeff m f) * m.prod fun s e => b s ^ e) : OC p) : ℂ_[p]))
        ((ev p f b : OC p) : ℂ_[p]) := fun b hb =>
    (hasSum_eval₂ continuous_algebraMap_OC (hasEval_of_norm_lt_one hb) f).map
      (OC p).subtype.toAddMonoidHom continuous_subtype_val
  have h := ((hev a (norm_pairPt_lt x.2 y.2)).sub (hev a' (norm_pairPt_lt x'.2 y.2))).sub
    ((hev (pairPt x.1 0) (norm_pairPt_lt x.2 (fun j => by simp))).sub
      (hev (pairPt x'.1 0) (norm_pairPt_lt x'.2 (fun j => by simp))))
  rw [F.ev_pair_zero x i, F.ev_pair_zero x' i] at h
  refine norm_le_of_hasSum h (mul_nonneg hr0 hδ) fun m => ?_
  rw [ha0, ha0']
  have hsplit : ∀ b χ : Fin 2 × Fin d → OC p,
      (φ (coeff m f) * m.prod fun s e => (b * χ) s ^ e) =
        (φ (coeff m f) * m.prod fun s e => b s ^ e) * m.prod fun s e => χ s ^ e := by
    intro b χ
    rw [mul_assoc, ← Finsupp.prod_mul]
    simp only [Pi.mul_apply, mul_pow]
  have hP0 : (m.prod fun s e => χ0 s ^ e) =
      if ∀ s ∈ m.support, s ∈ {s : Fin 2 × Fin d | s.1 = 0} then 1 else 0 := by
    convert prod_indicator (p := p) m {s : Fin 2 × Fin d | s.1 = 0}
  rw [hsplit a χ0, hsplit a' χ0, hP0]
  by_cases h0 : ∀ s ∈ m.support, s ∈ {s : Fin 2 × Fin d | s.1 = 0}
  · rw [if_pos h0]
    simpa using mul_nonneg hr0 hδ
  · rw [if_neg h0]
    simp only [mul_zero, ZeroMemClass.coe_zero, sub_zero, Subring.coe_mul]
    push Not at h0
    obtain ⟨s₁, hs₁, hs₁'⟩ := h0
    simp only [Set.mem_setOf_eq] at hs₁'
    have hs₁1 : s₁.1 = 1 := by
      rcases Fin.exists_fin_two.mp ⟨s₁.1, rfl⟩ with h | h
      · exact absurd h hs₁'
      · exact h
    have he : a s₁ = a' s₁ := by simp [a, a', pairPt, hs₁']
    have har : ‖((a s₁ : OC p) : ℂ_[p])‖ ≤ r := by simp only [a, pairPt, if_neg hs₁']; exact hy _
    have hab : ∀ s, ‖((a s : OC p) : ℂ_[p]) - a' s‖ ≤ δ := fun s => by
      simp only [a, a', pairPt]
      split_ifs
      · exact hxx _
      · simpa using hδ
    rw [← mul_sub, norm_mul]
    calc ‖((φ (coeff m f) : OC p) : ℂ_[p])‖ * ‖(((m.prod fun s e => a s ^ e) : OC p) : ℂ_[p]) -
          (((m.prod fun s e => a' s ^ e) : OC p) : ℂ_[p])‖ ≤ 1 * (r * δ) :=
          mul_le_mul (norm_OC_le _) (norm_monomial_sub_le' hr0 hr1 hδ hab m hs₁ he har)
            (norm_nonneg _) zero_le_one
      _ = r * δ := one_mul _

/-- **`Φ` is `1`-Lipschitz in the second variable up to `r δ`.** -/
theorem norm_add_sub_add_le' {x y y' : F.Pt p} {r δ : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hδ : 0 ≤ δ) (hx : F.Bnd x r) (hyy : ∀ j, ‖((y.1 j : OC p) : ℂ_[p]) - y'.1 j‖ ≤ δ)
    (i : Fin d) :
    ‖(((x + y).1 i : OC p) : ℂ_[p]) - (x + y').1 i - (y.1 i - y'.1 i)‖ ≤ r * δ := by
  rw [F.add_comm' x y, F.add_comm' x y']
  exact F.norm_add_sub_add_le hr0 hr1 hδ hx hyy i

/-- The point of the open polydisc with coordinates `v`. -/
def ofVec (v : Fin d → ℂ_[p]) (hv : ∀ j, ‖v j‖ < 1) : F.Pt p :=
  ⟨fun j => ⟨v j, (hv j).le⟩, hv⟩

omit [UniformSpace R] [DiscreteUniformity R] [Algebra R (OC p)] in
@[simp] theorem ofVec_val (v : Fin d → ℂ_[p]) (hv : ∀ j, ‖v j‖ < 1) (j : Fin d) :
    (((F.ofVec v hv).1 j : OC p) : ℂ_[p]) = v j := rfl

/-- The map whose fixed point is the inverse of `x`. -/
def negMap (x : F.Pt p) (v : Fin d → ℂ_[p]) : Fin d → ℂ_[p] :=
  if hv : ∀ j, ‖v j‖ < 1 then fun j => v j - (((x + F.ofVec v hv).1 j : OC p) : ℂ_[p]) else 0

/-- **Inverses** ([Hong, Lemma 2.2.5 (3)], on points): `x + y = 0` for some `y`, which may be
chosen in every closed polydisc of radius `r < 1` containing `x`. -/
theorem exists_neg_of_bnd (x : F.Pt p) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (hx : F.Bnd x r) :
    ∃ y : F.Pt p, F.Bnd y r ∧ x + y = 0 := by
  have hball : ∀ v : Fin d → ℂ_[p], (∀ j, ‖v j‖ ≤ r) → ∀ j, ‖v j‖ < 1 :=
    fun v hv j => (hv j).trans_lt hr1
  obtain ⟨v, hv, hfix⟩ := exists_fixed_of_contract (F.negMap x) hr0 hr0 hr1
    (fun v hv j => by
      rw [negMap, dif_pos (hball v hv)]
      have h := F.norm_add_sub_le hr0 hr1.le hx (y := F.ofVec v (hball v hv)) hv j
      rw [ofVec_val] at h
      have e : v j - (((x + F.ofVec v (hball v hv)).1 j : OC p) : ℂ_[p]) =
          -(((x + F.ofVec v (hball v hv)).1 j : OC p) - (x.1 j : ℂ_[p]) - v j) -
            (x.1 j : ℂ_[p]) := by ring
      rw [e]
      refine (norm_sub_le_max_Cp _ _).trans (max_le ?_ (hx j))
      rw [norm_neg]
      exact h.trans (by nlinarith))
    (fun v w hv hw δ hδ hvw j => by
      rw [negMap, negMap, dif_pos (hball v hv), dif_pos (hball w hw)]
      have h := F.norm_add_sub_add_le' hr0 hr1.le hδ hx (y := F.ofVec v (hball v hv))
        (y' := F.ofVec w (hball w hw)) (fun k => by simpa using hvw k) j
      simp only [ofVec_val] at h
      have e : v j - (((x + F.ofVec v (hball v hv)).1 j : OC p) : ℂ_[p]) -
          (w j - (((x + F.ofVec w (hball w hw)).1 j : OC p) : ℂ_[p])) =
          -((((x + F.ofVec v (hball v hv)).1 j : OC p) : ℂ_[p]) -
            ((x + F.ofVec w (hball w hw)).1 j : OC p) - (v j - w j)) := by ring
      rw [e, norm_neg]
      exact h)
  refine ⟨F.ofVec v (hball v hv), fun j => by simpa using hv j, F.pt_ext fun j => ?_⟩
  have h := congrFun hfix j
  rw [negMap, dif_pos (hball v hv)] at h
  apply Subtype.ext
  simpa using h

theorem exists_neg (x : F.Pt p) : ∃ y : F.Pt p, x + y = 0 := by
  obtain ⟨r, hr0, hr1, hr⟩ := exists_bound (fun j => ‖((x.1 j : OC p) : ℂ_[p])‖) x.2
  obtain ⟨y, -, hy⟩ := F.exists_neg_of_bnd x hr0 hr1 hr
  exact ⟨y, hy⟩

instance : Neg (F.Pt p) := ⟨fun x => (F.exists_neg x).choose⟩

theorem add_neg' (x : F.Pt p) : x + -x = 0 := (F.exists_neg x).choose_spec

/-- **`F(m_{ℂ_p})` is a commutative group.** -/
instance instAddCommGroupPt : AddCommGroup (F.Pt p) where
  __ := F.instAddCommMonoidPt
  neg_add_cancel x := by rw [F.add_comm', F.add_neg']
  zsmul := zsmulRec

/-- The radius `max_j |x_j|` of a point. -/
def rad (x : F.Pt p) : ℝ :=
  ((Finset.univ.sup fun j => ‖((x.1 j : OC p) : ℂ_[p])‖₊ : NNReal) : ℝ)

omit [UniformSpace R] [DiscreteUniformity R] [Algebra R (OC p)] in
theorem rad_nonneg (x : F.Pt p) : 0 ≤ F.rad x := NNReal.coe_nonneg _

omit [UniformSpace R] [DiscreteUniformity R] [Algebra R (OC p)] in
theorem bnd_rad (x : F.Pt p) : F.Bnd x (F.rad x) := fun j => by
  have h := Finset.le_sup (f := fun j => ‖((x.1 j : OC p) : ℂ_[p])‖₊) (Finset.mem_univ j)
  rw [← NNReal.coe_le_coe, coe_nnnorm] at h
  exact h

omit [UniformSpace R] [DiscreteUniformity R] [Algebra R (OC p)] in
theorem rad_le {x : F.Pt p} {r : ℝ} (hr : 0 ≤ r) (h : F.Bnd x r) : F.rad x ≤ r := by
  rw [rad, ← NNReal.coe_mk r hr, NNReal.coe_le_coe]
  refine Finset.sup_le fun j _ => ?_
  rw [← NNReal.coe_le_coe, coe_nnnorm, NNReal.coe_mk]
  exact h j

omit [UniformSpace R] [DiscreteUniformity R] [Algebra R (OC p)] in
theorem rad_lt_one (x : F.Pt p) : F.rad x < 1 := by
  obtain ⟨r, hr0, hr1, hr⟩ := exists_bound (fun j => ‖((x.1 j : OC p) : ℂ_[p])‖) x.2
  exact (F.rad_le hr0 hr).trans_lt hr1

/-- `−x` lies in every closed polydisc of radius `< 1` containing `x`. -/
theorem bnd_neg {x : F.Pt p} {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (hx : F.Bnd x r) :
    F.Bnd (-x) r := by
  set s := F.rad (-x)
  have hs0 : 0 ≤ s := F.rad_nonneg _
  have hs1 : s < 1 := F.rad_lt_one _
  set t := max r s
  have ht0 : 0 ≤ t := le_max_of_le_left hr0
  have ht1 : t ≤ 1 := (max_lt hr1 hs1).le
  have hy : ∀ j, ‖(((-x).1 j : OC p) : ℂ_[p])‖ ≤ max r (t ^ 2) := fun j => by
    have h := F.norm_add_sub_le ht0 ht1 (F.bnd_mono hx (le_max_left _ _))
      (F.bnd_mono (F.bnd_rad (-x)) (le_max_right _ _)) j
    rw [F.add_neg', zero_val, ZeroMemClass.coe_zero] at h
    have e : (((-x).1 j : OC p) : ℂ_[p]) =
        -((0 : ℂ_[p]) - (x.1 j : ℂ_[p]) - ((-x).1 j : ℂ_[p])) - (x.1 j : ℂ_[p]) := by ring
    rw [e]
    refine (norm_sub_le_max_Cp _ _).trans (max_le ?_ ?_)
    · rw [norm_neg]; exact h.trans (le_max_right _ _)
    · exact (hx j).trans (le_max_left _ _)
  have hsle : s ≤ max r (t ^ 2) := F.rad_le (le_max_of_le_left hr0) hy
  by_contra hcon
  have hrs : r < s := by
    by_contra h'
    exact hcon (F.bnd_mono (F.bnd_rad (-x)) (not_lt.mp h'))
  have ht : t = s := max_eq_right hrs.le
  rw [ht] at hsle
  rcases le_max_iff.mp hsle with h | h
  · exact absurd h (not_le.mpr hrs)
  · nlinarith

end FGL

end PadicHodge
