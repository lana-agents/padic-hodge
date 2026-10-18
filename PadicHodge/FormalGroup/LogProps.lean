/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.FormalGroup.Neg
import Mathlib.GroupTheory.Torsion

/-!
# Properties of the logarithm of a formal group law

For a formal group law `F` of dimension `d` (setting of `FormalGroup/Points.lean`) and the
logarithm `log_F : F(m_{ℂ_p}) → ℂ_p^d` of `FormalGroup/Log.lean` we prove [Hong, Prop. 3.3.6]:

* (1) `logHom`: `log_F` is a group homomorphism (`logF_add`, `logF_neg`, `logF_nsmul`);
* (2) `logF_bijOn`: **`log_F` is a local isomorphism**: for `0 ≤ r < |p|` it maps the closed
  polydisc `{|x_j| ≤ r}` of `F(m_{ℂ_p})` bijectively onto the closed polydisc `{|τ_j| ≤ r}` of
  `ℂ_p^d`; more precisely `|log_F(x) − x| ≤ r²/|p|` (`norm_logF_sub_le`) and
  `|(x − y) − (log_F x − log_F y)| ≤ (r/|p|) |x − y|` (`norm_sub_sub_logF_sub_le`), and the
  inverse is obtained from Banach's fixed point theorem (`exists_logF_eq`).
  [Hong] states (2) for `ν ≥ λ`, `λ ≥ 1` (i.e. `r ≤ |p|`) and leaves the proof as
  "straightforward"; for `p = 2`, `r = |2|` the statement fails (`log(1 + (−2)) = log(−1) = 0`
  for `Ĝ_m`), so we use `r < |p|`.
* (3) `logF_eq_zero_iff`: **`ker log_F` is the torsion subgroup** (`ker_logHom`);
* (4) `exists_logF_eq_pow_mul`: every `τ ∈ ℂ_p^d` is `p^{−n} log_F(x)`; together with (3) this
  says that `log_F` induces `F(m_{ℂ_p}) ⊗ ℚ ≅ ℂ_p^d`.
-/

noncomputable section

open MvPowerSeries Topology Filter Function Set

namespace PadicHodge

namespace FGL

variable {p : ℕ} [hp : Fact p.Prime] {R : Type*} [CommRing R] [UniformSpace R]
  [DiscreteUniformity R] [Algebra R (OC p)] {d : ℕ} (F : FGL R d)

theorem np_le_one : np p ≤ 1 := np_lt_one.le

theorem logF_zero (i : Fin d) : F.logF (0 : F.Pt p) i = 0 := by
  have h := F.logF_add (0 : F.Pt p) 0 i
  rw [add_zero] at h
  linear_combination -h

theorem logF_nsmul (n : ℕ) (x : F.Pt p) (i : Fin d) :
    F.logF (n • x) i = n * F.logF x i := by
  induction n with
  | zero => rw [zero_nsmul, logF_zero, Nat.cast_zero, zero_mul]
  | succ n ih => rw [succ_nsmul, F.logF_add, ih]; push_cast; ring

theorem logF_neg (x : F.Pt p) (i : Fin d) : F.logF (-x) i = -F.logF x i := by
  have h := F.logF_add x (-x) i
  rw [add_neg_cancel, logF_zero] at h
  linear_combination -h

theorem logF_sub (x y : F.Pt p) (i : Fin d) : F.logF (x - y) i = F.logF x i - F.logF y i := by
  rw [sub_eq_add_neg, logF_add, logF_neg, sub_eq_add_neg]

/-- **[Hong, Prop. 3.3.6 (1)]**: the logarithm as a group homomorphism `F(m_{ℂ_p}) → ℂ_p^d`. -/
def logHom : F.Pt p →+ (Fin d → ℂ_[p]) where
  toFun x i := F.logF x i
  map_zero' := funext F.logF_zero
  map_add' x y := funext (F.logF_add x y)

@[simp] theorem logHom_apply (x : F.Pt p) (i : Fin d) : F.logHom x i = F.logF x i := rfl

/-- On the polydisc of radius `s ≤ |p|`, multiplication by `p` multiplies the radius by `|p|`. -/
theorem bnd_pow_nsmul {x : F.Pt p} {s : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ np p) (hx : F.Bnd x s)
    (n : ℕ) : F.Bnd ((p ^ n) • x) (np p ^ n * s) := by
  induction n with
  | zero => simpa using hx
  | succ n ih =>
    rw [pow_succ, mul_nsmul]
    have h0 : 0 ≤ np p ^ n * s := mul_nonneg (pow_nonneg np_pos.le _) hs0
    have h1 : np p ^ n * s ≤ np p :=
      (mul_le_of_le_one_left hs0 (pow_le_one₀ np_pos.le np_le_one)).trans hs
    refine F.bnd_mono (F.bnd_p_nsmul h0 (h1.trans np_le_one) ih) (max_le ?_ ?_)
    · exact le_of_eq (by ring)
    · calc (np p ^ n * s) ^ 2 = (np p ^ n * s) * (np p ^ n * s) := sq _
        _ ≤ (np p ^ n * s) * np p := mul_le_mul_of_nonneg_left h1 h0
        _ = np p ^ (n + 1) * s := by ring

theorem norm_logSeq_sub_le {x : F.Pt p} {s : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ np p)
    (hx : F.Bnd x s) (i : Fin d) (n : ℕ) :
    ‖F.logSeq x i n - x.1 i‖ ≤ s ^ 2 / np p := by
  have hnp := np_pos (p := p)
  induction n with
  | zero =>
    simp only [logSeq, pow_zero, one_nsmul, div_one, sub_self, norm_zero]
    positivity
  | succ n ih =>
    have h0 : 0 ≤ np p ^ n * s := mul_nonneg (pow_nonneg hnp.le _) hs0
    have h1 : np p ^ n * s ≤ 1 :=
      (mul_le_of_le_one_left hs0 (pow_le_one₀ hnp.le np_le_one)).trans (hs.trans np_le_one)
    have hstep := F.norm_logSeq_succ_sub (i := i) h0 h1 (F.bnd_pow_nsmul hs0 hs hx n)
    have e : F.logSeq x i (n + 1) - x.1 i =
        (F.logSeq x i (n + 1) - F.logSeq x i n) + (F.logSeq x i n - x.1 i) := by ring
    rw [e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hstep.trans ?_) ih)
    have e2 : (np p ^ n * s) ^ 2 / np p ^ (n + 1) = s ^ 2 / np p * np p ^ n := by
      field_simp
      ring
    rw [e2]
    exact mul_le_of_le_one_right (by positivity) (pow_le_one₀ hnp.le np_le_one)

/-- **`|log_F(x) − x| ≤ s²/|p|`** on the polydisc of radius `s ≤ |p|`. -/
theorem norm_logF_sub_le {x : F.Pt p} {s : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ np p)
    (hx : F.Bnd x s) (i : Fin d) : ‖F.logF x i - x.1 i‖ ≤ s ^ 2 / np p :=
  le_of_tendsto' ((continuous_norm.tendsto _).comp ((F.tendsto_logSeq x i).sub_const _))
    fun n => F.norm_logSeq_sub_le hs0 hs hx i n

theorem norm_logF_le {x : F.Pt p} {s : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ np p)
    (hx : F.Bnd x s) (i : Fin d) : ‖F.logF x i‖ ≤ s := by
  have h := F.norm_logF_sub_le hs0 hs hx i
  have e : F.logF x i = (F.logF x i - x.1 i) + x.1 i := by ring
  rw [e]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (h.trans ?_) (hx i))
  rw [div_le_iff₀ np_pos]
  nlinarith

/-- A point of radius `< |p|` with vanishing logarithm is `0`. -/
theorem eq_zero_of_logF_eq_zero {x : F.Pt p} {s : ℝ} (hs0 : 0 ≤ s) (hs : s < np p)
    (hx : F.Bnd x s) (h : ∀ i, F.logF x i = 0) : x = 0 := by
  set t := F.rad x
  have ht0 : 0 ≤ t := F.rad_nonneg x
  have hts : t ≤ s := F.rad_le hs0 hx
  have hb : ∀ i, ‖((x.1 i : OC p) : ℂ_[p])‖ ≤ t ^ 2 / np p := fun i => by
    have := F.norm_logF_sub_le ht0 (hts.trans hs.le) (F.bnd_rad x) i
    rwa [h i, zero_sub, norm_neg] at this
  have htt : t ≤ t ^ 2 / np p := F.rad_le (by have := np_pos (p := p); positivity) hb
  have ht : t = 0 := by
    by_contra hne
    have tpos : 0 < t := lt_of_le_of_ne ht0 (Ne.symm hne)
    rw [le_div_iff₀ np_pos] at htt
    nlinarith
  refine F.pt_ext fun j => Subtype.ext ?_
  have := F.bnd_rad x j
  rw [show F.rad x = 0 from ht] at this
  rw [zero_val, ZeroMemClass.coe_zero]
  exact norm_le_zero_iff.mp this

theorem bnd_sub {x y : F.Pt p} {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (hx : F.Bnd x r)
    (hy : F.Bnd y r) : F.Bnd (x - y) r := fun j => by
  have hny := F.bnd_neg hr0 hr1 hy
  have h := F.norm_add_sub_le hr0 hr1.le hx hny j
  rw [sub_eq_add_neg]
  have e : (((x + -y).1 j : OC p) : ℂ_[p]) =
      ((((x + -y).1 j : OC p) : ℂ_[p]) - x.1 j - (-y).1 j) + x.1 j + (-y).1 j := by ring
  rw [e]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ (hny j))
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (h.trans ?_) (hx j))
  nlinarith

/-- **Injectivity of `log_F` on the polydisc of radius `r < |p|`.** -/
theorem logF_injOn {x y : F.Pt p} {r : ℝ} (hr0 : 0 ≤ r) (hr : r < np p) (hx : F.Bnd x r)
    (hy : F.Bnd y r) (h : ∀ i, F.logF x i = F.logF y i) : x = y := by
  have hz := F.bnd_sub hr0 (hr.trans np_lt_one) hx hy
  have := F.eq_zero_of_logF_eq_zero hr0 hr hz fun i => by rw [logF_sub, h, sub_self]
  exact sub_eq_zero.mp this

/-- **`log_F` is a contraction-perturbation of the identity** on the polydisc of radius
`r ≤ |p|`: `|(x − y) − (log_F x − log_F y)| ≤ (r/|p|) δ` if `|x_j − y_j| ≤ δ`. -/
theorem norm_sub_sub_logF_sub_le {x y : F.Pt p} {r δ : ℝ} (hr0 : 0 ≤ r) (hr : r ≤ np p)
    (hx : F.Bnd x r) (hy : F.Bnd y r) (hδ : 0 ≤ δ)
    (hxy : ∀ j, ‖((x.1 j : OC p) : ℂ_[p]) - y.1 j‖ ≤ δ) (i : Fin d) :
    ‖(((x.1 i : OC p) : ℂ_[p]) - y.1 i) - (F.logF x i - F.logF y i)‖ ≤ r / np p * δ := by
  have hnp := np_pos (p := p)
  have hr1 : r < 1 := hr.trans_lt np_lt_one
  set δ' := min δ r
  have hδ'0 : 0 ≤ δ' := le_min hδ hr0
  have hδ'r : δ' ≤ r := min_le_right _ _
  have hxy' : ∀ j, ‖((x.1 j : OC p) : ℂ_[p]) - y.1 j‖ ≤ δ' := fun j =>
    le_min (hxy j) ((norm_sub_le_max_Cp _ _).trans (max_le (hx j) (hy j)))
  have hny := F.bnd_neg hr0 hr1 hy
  have hlin : ∀ j, ‖(((x - y).1 j : OC p) : ℂ_[p]) - (x.1 j - y.1 j)‖ ≤ r * δ' := fun j => by
    have h := F.norm_add_sub_add_le hr0 hr1.le hδ'0 hny hxy' j
    rwa [add_neg_cancel, zero_val, ZeroMemClass.coe_zero, sub_zero, ← sub_eq_add_neg] at h
  have hz : F.Bnd (x - y) δ' := fun j => by
    have e : (((x - y).1 j : OC p) : ℂ_[p]) =
        ((((x - y).1 j : OC p) : ℂ_[p]) - (x.1 j - y.1 j)) + (x.1 j - y.1 j) := by ring
    rw [e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ((hlin j).trans ?_) (hxy' j))
    nlinarith
  have hlog := F.norm_logF_sub_le hδ'0 (hδ'r.trans hr) hz i
  rw [logF_sub] at hlog
  have e : (((x.1 i : OC p) : ℂ_[p]) - y.1 i) - (F.logF x i - F.logF y i) =
      -((((x - y).1 i : OC p) : ℂ_[p]) - (x.1 i - y.1 i)) -
        ((F.logF x i - F.logF y i) - ((x - y).1 i : ℂ_[p])) := by ring
  rw [e]
  refine (norm_sub_le_max_Cp _ _).trans (max_le ?_ ?_)
  · rw [norm_neg]
    refine (hlin i).trans ?_
    calc r * δ' ≤ r / np p * δ' :=
          mul_le_mul_of_nonneg_right (le_div_self hr0 hnp np_le_one) hδ'0
      _ ≤ r / np p * δ :=
          mul_le_mul_of_nonneg_left (min_le_left _ _) (div_nonneg hr0 hnp.le)
  · refine hlog.trans ?_
    calc δ' ^ 2 / np p ≤ r / np p * δ' := by
          rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hnp]
          nlinarith
      _ ≤ r / np p * δ :=
          mul_le_mul_of_nonneg_left (min_le_left _ _) (div_nonneg hr0 hnp.le)

/-- The map whose fixed point is `log_F^{-1}(τ)`. -/
def logInvMap (τ : Fin d → ℂ_[p]) (v : Fin d → ℂ_[p]) : Fin d → ℂ_[p] :=
  if hv : ∀ j, ‖v j‖ < 1 then fun j => τ j + v j - F.logF (F.ofVec v hv) j else 0

/-- **Surjectivity of `log_F` onto the polydisc of radius `r < |p|`.** -/
theorem exists_logF_eq {τ : Fin d → ℂ_[p]} {r : ℝ} (hr0 : 0 ≤ r) (hr : r < np p)
    (hτ : ∀ i, ‖τ i‖ ≤ r) : ∃ x : F.Pt p, F.Bnd x r ∧ ∀ i, F.logF x i = τ i := by
  have hnp := np_pos (p := p)
  have hr1 : r < 1 := hr.trans np_lt_one
  have hball : ∀ v : Fin d → ℂ_[p], (∀ j, ‖v j‖ ≤ r) → ∀ j, ‖v j‖ < 1 :=
    fun v hv j => (hv j).trans_lt hr1
  have hB : ∀ (v : Fin d → ℂ_[p]) (hv : ∀ j, ‖v j‖ ≤ r), F.Bnd (F.ofVec v (hball v hv)) r :=
    fun v hv j => by simpa using hv j
  obtain ⟨v, hv, hfix⟩ := exists_fixed_of_contract (F.logInvMap τ) hr0
    (div_nonneg hr0 hnp.le) ((div_lt_one hnp).mpr hr)
    (fun v hv j => by
      rw [logInvMap, dif_pos (hball v hv)]
      have h := F.norm_logF_sub_le hr0 hr.le (hB v hv) j
      rw [ofVec_val] at h
      have e : τ j + v j - F.logF (F.ofVec v (hball v hv)) j =
          τ j - (F.logF (F.ofVec v (hball v hv)) j - v j) := by ring
      rw [e]
      refine (norm_sub_le_max_Cp _ _).trans (max_le (hτ j) (h.trans ?_))
      rw [div_le_iff₀ hnp]
      nlinarith)
    (fun v w hv hw δ hδ hvw j => by
      rw [logInvMap, logInvMap, dif_pos (hball v hv), dif_pos (hball w hw)]
      have h := F.norm_sub_sub_logF_sub_le hr0 hr.le (hB v hv) (hB w hw) hδ
        (fun k => by simpa using hvw k) j
      simp only [ofVec_val] at h
      have e : τ j + v j - F.logF (F.ofVec v (hball v hv)) j -
          (τ j + w j - F.logF (F.ofVec w (hball w hw)) j) =
          (v j - w j) - (F.logF (F.ofVec v (hball v hv)) j -
            F.logF (F.ofVec w (hball w hw)) j) := by ring
      rw [e]
      exact h)
  refine ⟨F.ofVec v (hball v hv), hB v hv, fun i => ?_⟩
  have h := congrFun hfix i
  rw [logInvMap, dif_pos (hball v hv)] at h
  linear_combination -h

/-- **[Hong, Prop. 3.3.6 (2)]**: for `0 ≤ r < |p|`, `log_F` maps the closed polydisc of radius
`r` of `F(m_{ℂ_p})` bijectively onto the closed polydisc of radius `r` of `ℂ_p^d`. -/
theorem logF_bijOn {r : ℝ} (hr0 : 0 ≤ r) (hr : r < np p) :
    BijOn (F.logHom (p := p)) {x | F.Bnd x r} {τ | ∀ i, ‖τ i‖ ≤ r} :=
  ⟨fun _ hx i => F.norm_logF_le hr0 hr.le hx i,
    fun _ hx _ hy h => F.logF_injOn hr0 hr hx hy fun i => congrFun h i,
    fun _ hτ => by
      obtain ⟨x, hx, hlog⟩ := F.exists_logF_eq hr0 hr hτ
      exact ⟨x, hx, funext hlog⟩⟩

/-- **[Hong, Prop. 3.3.6 (3)]**: `log_F(x) = 0` iff `x` is torsion. -/
theorem logF_eq_zero_iff (x : F.Pt p) : (∀ i, F.logF x i = 0) ↔ IsOfFinAddOrder x := by
  have hnp := np_pos (p := p)
  constructor
  · intro h
    obtain ⟨N, hN⟩ := F.exists_bnd_pow x
    have hb := hN (N + 1) (by omega)
    rw [show N + 1 - N + 1 = 2 by omega] at hb
    have hlt : np p ^ 2 < np p := by
      rw [sq]; exact mul_lt_of_lt_one_left hnp np_lt_one
    have h0 := F.eq_zero_of_logF_eq_zero (by positivity) hlt hb fun i => by
      rw [logF_nsmul, h i, mul_zero]
    exact isOfFinAddOrder_iff_nsmul_eq_zero.mpr
      ⟨p ^ (N + 1), pow_pos (Fact.out : p.Prime).pos _, h0⟩
  · intro h i
    obtain ⟨n, hn, hnx⟩ := isOfFinAddOrder_iff_nsmul_eq_zero.mp h
    have e := F.logF_nsmul n x i
    rw [hnx, logF_zero] at e
    have hn' : (n : ℂ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
    exact (mul_eq_zero.mp e.symm).resolve_left hn'

/-- **[Hong, Prop. 3.3.6 (3)]**: `ker log_F = F(m_{ℂ_p})_{tors}`. -/
theorem ker_logHom : F.logHom.ker = AddCommGroup.torsion (F.Pt p) := by
  ext x
  rw [AddMonoidHom.mem_ker, AddCommGroup.mem_torsion, ← F.logF_eq_zero_iff]
  exact funext_iff

/-- **[Hong, Prop. 3.3.6 (4)]**: every `τ ∈ ℂ_p^d` is `p^{−n} log_F(x)` for some point `x`. -/
theorem exists_logF_eq_pow_mul (τ : Fin d → ℂ_[p]) :
    ∃ (x : F.Pt p) (n : ℕ), ∀ i, F.logF x i = (p : ℂ_[p]) ^ n * τ i := by
  have hnp := np_pos (p := p)
  obtain ⟨M, hM0, hM⟩ : ∃ M : ℝ, 0 ≤ M ∧ ∀ i, ‖τ i‖ ≤ M :=
    ⟨∑ i, ‖τ i‖, Finset.sum_nonneg fun i _ => norm_nonneg _,
      fun i => Finset.single_le_sum (fun j _ => norm_nonneg (τ j)) (Finset.mem_univ i)⟩
  have hlt : np p ^ 2 < np p := by rw [sq]; exact mul_lt_of_lt_one_left hnp np_lt_one
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (div_pos (pow_pos hnp 2) (by linarith : 0 < M + 1))
    (np_lt_one (p := p))
  have hτ : ∀ i, ‖(p : ℂ_[p]) ^ n * τ i‖ ≤ np p ^ 2 := fun i => by
    rw [norm_mul, norm_pow]
    rw [lt_div_iff₀ (by linarith)] at hn
    calc np p ^ n * ‖τ i‖ ≤ np p ^ n * (M + 1) :=
          mul_le_mul_of_nonneg_left ((hM i).trans (by linarith)) (pow_nonneg hnp.le _)
      _ ≤ np p ^ 2 := hn.le
  obtain ⟨x, -, hx⟩ := F.exists_logF_eq (by positivity) hlt hτ
  exact ⟨x, n, hx⟩

end FGL

end PadicHodge
