/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.FormalGroup.Points

/-!
# The logarithm of a formal group law on `m_{ℂ_p}^d`

For a formal group law `F` of dimension `d` over `R` (discrete) with `R → O_{ℂ_p}` and points
`x ∈ F(m_{ℂ_p})` ([Hong, §3.3], [Stix, §11.3]):

* `norm_add_sub_le`: `|Φ_i(x, y) − x_i − y_i| ≤ r²` if `|x_j|, |y_j| ≤ r ≤ 1` (the monomials of
  `Φ_i` involving both `T` and `U` have degree `≥ 2`; the others give `Φ_i(x, 0) = x_i` and
  `Φ_i(0, y) = y_i`);
* `bnd_nsmul`, `bnd_p_nsmul`: `|(n·x)_i − n x_i| ≤ r²`, so `p·x` has radius `≤ max(|p| r, r²)`
  ([Hong, Lemma 3.3.2]);
* `exists_bnd_pow`: `p^n x` has radius `≤ |p|^{n−N+1}` for `n ≥ N`;
* **`tendsto_logSeq`**: `(p^n x)_i / p^n` converges ([Hong, Lemma 3.3.3]); its limit is
  `logF F x i` ([Hong, Def. 3.3.4]);
* **`logF_add`**: `log_F(x +_F y) = log_F(x) + log_F(y)` ([Hong, Prop. 3.3.6 (1)]).
-/

noncomputable section

open MvPowerSeries Topology Filter

namespace PadicHodge

namespace FGL

variable {p : ℕ} [hp : Fact p.Prime] {R : Type*} [CommRing R] [UniformSpace R]
  [DiscreteUniformity R] [Algebra R (OC p)] {d : ℕ} (F : FGL R d)

/-- `x` lies in the closed polydisc of radius `r`. -/
def Bnd (x : F.Pt p) (r : ℝ) : Prop := ∀ j, ‖((x.1 j : OC p) : ℂ_[p])‖ ≤ r

/-- `|p|` in `ℂ_p`. -/
abbrev np (p : ℕ) [Fact p.Prime] : ℝ := ‖(p : ℂ_[p])‖

theorem np_pos : 0 < np p := by
  rw [norm_pos_iff]; exact_mod_cast (Fact.out : p.Prime).ne_zero

theorem np_lt_one : np p < 1 := by
  have : ((p : ℚ_[p]) : ℂ_[p]) = (p : ℂ_[p]) := by simp
  rw [np, ← this, PadicComplex.norm_extends', Padic.norm_p]
  exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt)

/-- Products of powers of the coordinates of a point of radius `r ≤ 1`. -/
theorem norm_monomial_le {σ : Type*} {a : σ → OC p} {r : ℝ}
    (har : ∀ s, ‖((a s : OC p) : ℂ_[p])‖ ≤ r) (m : σ →₀ ℕ) :
    ‖(((m.prod fun s e => a s ^ e) : OC p) : ℂ_[p])‖ ≤ r ^ m.degree := by
  have : (((m.prod fun s e => a s ^ e) : OC p) : ℂ_[p]) =
      (OC p).subtype (m.prod fun s e => a s ^ e) := rfl
  rw [this, map_finsuppProd, Finsupp.prod, norm_prod, Finsupp.degree_apply,
    ← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_le_prod (fun s _ => norm_nonneg _) fun s _ => ?_
  rw [map_pow, norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (har s) _

/-- Products of the indicator of a set of variables. -/
theorem prod_indicator {σ : Type*} (m : σ →₀ ℕ) (S : Set σ) [DecidablePred (· ∈ S)] :
    (m.prod fun s e => (if s ∈ S then (1 : OC p) else 0) ^ e) =
      if ∀ s ∈ m.support, s ∈ S then 1 else 0 := by
  unfold Finsupp.prod
  split_ifs with h
  · exact Finset.prod_eq_one fun s hs => by
      change (if s ∈ S then (1 : OC p) else 0) ^ m s = 1
      rw [if_pos (h s hs), one_pow]
  · push Not at h
    obtain ⟨s, hs, hsS⟩ := h
    refine Finset.prod_eq_zero hs ?_
    change (if s ∈ S then (1 : OC p) else 0) ^ m s = 0
    rw [if_neg hsS, zero_pow (Finsupp.mem_support_iff.mp hs)]

theorem ev_pair_zero (x : F.Pt p) (i : Fin d) :
    ev p (F.Φ i) (pairPt x.1 (0 : Fin d → OC p)) = x.1 i := by
  have := congrArg (fun z : F.Pt p => z.1 i) (F.add_zero' x)
  exact this

theorem ev_zero_pair (y : F.Pt p) (i : Fin d) :
    ev p (F.Φ i) (pairPt (0 : Fin d → OC p) y.1) = y.1 i := by
  have := congrArg (fun z : F.Pt p => z.1 i) (add_zero' F y)
  rw [← this, F.add_comm']
  rfl

/-- **`|Φ_i(x, y) − x_i − y_i| ≤ r²`.** -/
theorem norm_add_sub_le {x y : F.Pt p} {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hx : F.Bnd x r)
    (hy : F.Bnd y r) (i : Fin d) :
    ‖(((x + y).1 i : OC p) : ℂ_[p]) - x.1 i - y.1 i‖ ≤ r ^ 2 := by
  classical
  set f := F.Φ i
  set φ := algebraMap R (OC p)
  let a : Fin 2 × Fin d → OC p := pairPt x.1 y.1
  let χ0 : Fin 2 × Fin d → OC p := fun s => if s ∈ {s : Fin 2 × Fin d | s.1 = 0} then 1 else 0
  let χ1 : Fin 2 × Fin d → OC p := fun s => if s ∈ {s : Fin 2 × Fin d | s.1 = 1} then 1 else 0
  have ha0 : pairPt x.1 (0 : Fin d → OC p) = a * χ0 := by
    funext ⟨c, j⟩
    fin_cases c <;> simp [a, χ0, pairPt]
  have ha1 : pairPt (0 : Fin d → OC p) y.1 = a * χ1 := by
    funext ⟨c, j⟩
    fin_cases c <;> simp [a, χ1, pairPt]
  have har : ∀ s, ‖((a s : OC p) : ℂ_[p])‖ ≤ r := fun s => by
    simp only [a, pairPt]; split_ifs; exacts [hx _, hy _]
  have hev : ∀ b : Fin 2 × Fin d → OC p, (∀ s, ‖((b s : OC p) : ℂ_[p])‖ < 1) →
      HasSum (fun m => (((φ (coeff m f) * m.prod fun s e => b s ^ e) : OC p) : ℂ_[p]))
        ((ev p f b : OC p) : ℂ_[p]) := fun b hb =>
    (hasSum_eval₂ continuous_algebraMap_OC (hasEval_of_norm_lt_one hb) f).map
      (OC p).subtype.toAddMonoidHom continuous_subtype_val
  have hxl := fun j => x.2 j
  have hyl := fun j => y.2 j
  have h := ((hev a (norm_pairPt_lt x.2 y.2)).sub
    (hev (pairPt x.1 0) (norm_pairPt_lt x.2 (fun j => by simp)))).sub
    (hev (pairPt 0 y.1) (norm_pairPt_lt (fun j => by simp) y.2))
  rw [F.ev_pair_zero x i, F.ev_zero_pair y i] at h
  refine norm_le_of_hasSum h (sq_nonneg r) fun m => ?_
  rw [ha0, ha1]
  have hprod : ∀ χ : Fin 2 × Fin d → OC p, (m.prod fun s e => (a * χ) s ^ e) =
      (m.prod fun s e => a s ^ e) * (m.prod fun s e => χ s ^ e) := fun χ => by
    simp only [Pi.mul_apply, mul_pow]
    exact Finsupp.prod_mul
  set g : OC p := φ (coeff m f) * m.prod fun s e => a s ^ e with hg
  have hsplit : ∀ χ : Fin 2 × Fin d → OC p, (φ (coeff m f) * m.prod fun s e => (a * χ) s ^ e) =
      g * m.prod fun s e => χ s ^ e := fun χ => by rw [hprod, hg, mul_assoc]
  have hP0 : (m.prod fun s e => χ0 s ^ e) =
      if ∀ s ∈ m.support, s ∈ {s : Fin 2 × Fin d | s.1 = 0} then 1 else 0 := by
    convert prod_indicator (p := p) m {s : Fin 2 × Fin d | s.1 = 0}
  have hP1 : (m.prod fun s e => χ1 s ^ e) =
      if ∀ s ∈ m.support, s ∈ {s : Fin 2 × Fin d | s.1 = 1} then 1 else 0 := by
    convert prod_indicator (p := p) m {s : Fin 2 × Fin d | s.1 = 1}
  rw [hsplit χ0, hsplit χ1, hP0, hP1]
  have hgle : ‖((g : OC p) : ℂ_[p])‖ ≤ r ^ m.degree := by
    rw [hg, Subring.coe_mul, norm_mul]
    calc ‖((φ (coeff m f) : OC p) : ℂ_[p])‖ * ‖(((m.prod fun s e => a s ^ e) : OC p) : ℂ_[p])‖
        ≤ 1 * r ^ m.degree :=
          mul_le_mul (norm_OC_le _) (norm_monomial_le har m) (norm_nonneg _) zero_le_one
      _ = r ^ m.degree := one_mul _
  by_cases h0 : ∀ s ∈ m.support, s ∈ {s : Fin 2 × Fin d | s.1 = 0} <;>
    by_cases h1 : ∀ s ∈ m.support, s ∈ {s : Fin 2 × Fin d | s.1 = 1}
  · -- `m = 0`
    have hm : m = 0 := by
      ext s
      by_contra hs
      have hs' : s ∈ m.support := Finsupp.mem_support_iff.mpr hs
      have e0 := h0 s hs'
      have e1 := h1 s hs'
      simp only [Set.mem_setOf_eq] at e0 e1
      rw [e0] at e1
      exact absurd e1 (by decide)
    have : g = 0 := by
      rw [hg, hm, coeff_zero_eq_constantCoeff_apply, F.constantCoeff_Φ i, map_zero, zero_mul]
    rw [this]
    simpa using sq_nonneg r
  · rw [if_pos h0, if_neg h1]
    simpa using sq_nonneg r
  · rw [if_neg h0, if_pos h1]
    simpa using sq_nonneg r
  · -- mixed monomials have degree `≥ 2`
    rw [if_neg h0, if_neg h1]
    simp only [mul_zero, ZeroMemClass.coe_zero, sub_zero]
    push Not at h0 h1
    obtain ⟨s0, hs0, hs0'⟩ := h0
    obtain ⟨s1, hs1, hs1'⟩ := h1
    simp only [Set.mem_setOf_eq] at hs0' hs1'
    have hne : s0 ≠ s1 := by
      rintro rfl
      rcases Fin.exists_fin_two.mp ⟨s0.1, rfl⟩ with h | h
      · exact hs0' h
      · exact hs1' h
    have hdeg : 2 ≤ m.degree := by
      rw [Finsupp.degree_apply]
      have hsub : ({s0, s1} : Finset (Fin 2 × Fin d)) ⊆ m.support := by
        intro s hs
        simp only [Finset.mem_insert, Finset.mem_singleton] at hs
        rcases hs with rfl | rfl <;> assumption
      calc 2 ≤ m s0 + m s1 := by
            have := Finsupp.mem_support_iff.mp hs0
            have := Finsupp.mem_support_iff.mp hs1
            omega
        _ = ∑ s ∈ ({s0, s1} : Finset _), m s := (Finset.sum_pair hne).symm
        _ ≤ ∑ s ∈ m.support, m s := Finset.sum_le_sum_of_subset hsub
    exact hgle.trans (pow_le_pow_of_le_one hr0 hr1 hdeg)

/-- **`|(n·x)_i − n x_i| ≤ r²`**, and `n·x` stays in the polydisc of radius `r`. -/
theorem bnd_nsmul {x : F.Pt p} {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hx : F.Bnd x r) (n : ℕ) :
    F.Bnd (n • x) r ∧ ∀ i, ‖(((n • x).1 i : OC p) : ℂ_[p]) - n * x.1 i‖ ≤ r ^ 2 := by
  induction n with
  | zero =>
    refine ⟨fun j => ?_, fun i => ?_⟩
    · rw [zero_nsmul]; simp [hr0]
    · rw [zero_nsmul]; simp [sq_nonneg]
  | succ n ih =>
    have hr2 : r ^ 2 ≤ r := by nlinarith
    have hsub := F.norm_add_sub_le hr0 hr1 ih.1 hx
    rw [succ_nsmul]
    refine ⟨fun j => ?_, fun i => ?_⟩
    · have e : (((n • x + x).1 j : OC p) : ℂ_[p]) =
          ((((n • x + x).1 j : OC p) : ℂ_[p]) - (n • x).1 j - x.1 j) + (n • x).1 j + x.1 j := by
        ring
      rw [e]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ (hx j))
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ((hsub j).trans hr2) (ih.1 j))
    · have e : (((n • x + x).1 i : OC p) : ℂ_[p]) - ((n + 1 : ℕ) : ℂ_[p]) * x.1 i =
          ((((n • x + x).1 i : OC p) : ℂ_[p]) - (n • x).1 i - x.1 i) +
            ((((n • x).1 i : OC p) : ℂ_[p]) - n * x.1 i) := by
        push_cast; ring
      rw [e]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hsub i) (ih.2 i))

/-- **[Hong, Lemma 3.3.2]**: `p·x` has radius `≤ max(|p| r, r²)`. -/
theorem bnd_p_nsmul {x : F.Pt p} {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hx : F.Bnd x r) :
    F.Bnd (p • x) (max (np p * r) (r ^ 2)) := by
  intro j
  have h := (F.bnd_nsmul hr0 hr1 hx p).2 j
  have e : (((p • x).1 j : OC p) : ℂ_[p]) =
      ((((p • x).1 j : OC p) : ℂ_[p]) - p * x.1 j) + p * x.1 j := by ring
  rw [e]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans ?_
  rw [max_comm]
  refine max_le_max ?_ h
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (hx j) (norm_nonneg _)

omit [UniformSpace R] [DiscreteUniformity R] [Algebra R (OC p)] in
theorem bnd_mono {x : F.Pt p} {r s : ℝ} (hx : F.Bnd x r) (hrs : r ≤ s) : F.Bnd x s :=
  fun j => (hx j).trans hrs

/-- **`p^n x → 0`**: eventually `p^n x` has radius `≤ |p|^{n − N + 1}`. -/
theorem exists_bnd_pow (x : F.Pt p) :
    ∃ N, ∀ n, N ≤ n → F.Bnd ((p ^ n) • x) (np p ^ (n - N + 1)) := by
  obtain ⟨r0, hr0, hr1, hr⟩ := exists_bound (fun j => ‖((x.1 j : OC p) : ℂ_[p])‖) x.2
  set ρ := max (np p) r0
  have hρ1 : ρ < 1 := max_lt np_lt_one hr1
  have hρ0 : 0 ≤ ρ := le_max_of_le_left np_pos.le
  -- contraction: radius `r0 ρ^n`
  have hc : ∀ n, F.Bnd ((p ^ n) • x) (r0 * ρ ^ n) := by
    intro n
    induction n with
    | zero => rw [pow_zero, one_nsmul, pow_zero, mul_one]; exact hr
    | succ n ih =>
      rw [pow_succ, mul_nsmul]
      have hs0 : 0 ≤ r0 * ρ ^ n := mul_nonneg hr0 (pow_nonneg hρ0 _)
      have hs1 : r0 * ρ ^ n ≤ r0 := mul_le_of_le_one_right hr0 (pow_le_one₀ hρ0 hρ1.le)
      refine F.bnd_mono (F.bnd_p_nsmul hs0 (hs1.trans hr1.le) ih) (max_le ?_ ?_)
      · calc np p * (r0 * ρ ^ n) ≤ ρ * (r0 * ρ ^ n) :=
              mul_le_mul_of_nonneg_right (le_max_left _ _) hs0
          _ = r0 * ρ ^ (n + 1) := by ring
      · calc (r0 * ρ ^ n) ^ 2 = (r0 * ρ ^ n) * (r0 * ρ ^ n) := sq _
          _ ≤ (r0 * ρ ^ n) * ρ := mul_le_mul_of_nonneg_left (hs1.trans (le_max_right _ _)) hs0
          _ = r0 * ρ ^ (n + 1) := by ring
  obtain ⟨N, hN⟩ : ∃ N, r0 * ρ ^ N ≤ np p := by
    rcases eq_or_lt_of_le hr0 with h | h
    · exact ⟨0, by rw [← h, zero_mul]; exact np_pos.le⟩
    · obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (div_pos (np_pos (p := p)) h) hρ1
      refine ⟨N, ?_⟩
      rw [lt_div_iff₀ h, mul_comm] at hN
      exact hN.le
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [Nat.add_sub_cancel_left]
  induction k with
  | zero => rw [add_zero, zero_add, pow_one]; exact F.bnd_mono (hc N) hN
  | succ k ih =>
    have ih' := ih (by omega)
    rw [← add_assoc, pow_succ, mul_nsmul]
    have hs0 : 0 ≤ np p ^ (k + 1) := pow_nonneg np_pos.le _
    have hs1 : np p ^ (k + 1) ≤ np p := pow_le_of_le_one np_pos.le np_lt_one.le (by omega)
    refine F.bnd_mono (F.bnd_p_nsmul hs0 (hs1.trans np_lt_one.le) ih') (max_le ?_ ?_)
    · calc np p * np p ^ (k + 1) = np p ^ (k + 1 + 1) := by ring
        _ ≤ np p ^ (k + 1 + 1) := le_rfl
    · calc (np p ^ (k + 1)) ^ 2 = np p ^ (k + 1) * np p ^ (k + 1) := sq _
        _ ≤ np p * np p ^ (k + 1) := mul_le_mul_of_nonneg_right hs1 hs0
        _ = np p ^ (k + 1 + 1) := by ring

/-- `(p^n x)_i / p^n`. -/
def logSeq (x : F.Pt p) (i : Fin d) (n : ℕ) : ℂ_[p] :=
  ((((p ^ n) • x).1 i : OC p) : ℂ_[p]) / (p : ℂ_[p]) ^ n

theorem p_ne_zero' : (p : ℂ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero

/-- The step estimate `|logSeq (n+1) − logSeq n| ≤ s² / |p|^{n+1}` for `p^n x` of radius `s`. -/
theorem norm_logSeq_succ_sub {x : F.Pt p} {i : Fin d} {n : ℕ} {s : ℝ} (hs0 : 0 ≤ s)
    (hs1 : s ≤ 1) (hs : F.Bnd ((p ^ n) • x) s) :
    ‖F.logSeq x i (n + 1) - F.logSeq x i n‖ ≤ s ^ 2 / np p ^ (n + 1) := by
  have h := (F.bnd_nsmul hs0 hs1 hs p).2 i
  have e : F.logSeq x i (n + 1) - F.logSeq x i n =
      (((((p • ((p ^ n) • x)).1 i : OC p) : ℂ_[p]) - p * ((p ^ n) • x).1 i)) /
        (p : ℂ_[p]) ^ (n + 1) := by
    rw [logSeq, logSeq, pow_succ, mul_nsmul]
    have hp := p_ne_zero' (p := p)
    field_simp
    ring
  rw [e, norm_div, norm_pow]
  exact div_le_div_of_nonneg_right h (pow_nonneg (norm_nonneg _) _)

theorem cauchySeq_logSeq (x : F.Pt p) (i : Fin d) : CauchySeq (F.logSeq x i) := by
  obtain ⟨N, hN⟩ := F.exists_bnd_pow x
  have hshift : CauchySeq fun k => F.logSeq x i (N + k) := by
    refine cauchySeq_of_le_geometric (np p) (np p / np p ^ N) np_lt_one fun k => ?_
    rw [dist_comm, dist_eq_norm]
    have hb := hN (N + k) (by omega)
    rw [Nat.add_sub_cancel_left] at hb
    have hs1 : np p ^ (k + 1) ≤ 1 := pow_le_one₀ np_pos.le np_lt_one.le
    refine (F.norm_logSeq_succ_sub (pow_nonneg np_pos.le _) hs1 hb).trans (le_of_eq ?_)
    have hp0 := np_pos (p := p)
    field_simp
    ring
  exact (cauchySeq_shift N).mp (by simpa [add_comm] using hshift)

/-- **The logarithm** `log_F(x)_i = lim (p^n x)_i / p^n` ([Hong, Def. 3.3.4]). -/
def logF (x : F.Pt p) (i : Fin d) : ℂ_[p] := limUnder atTop (F.logSeq x i)

theorem tendsto_logSeq (x : F.Pt p) (i : Fin d) :
    Tendsto (F.logSeq x i) atTop (𝓝 (F.logF x i)) :=
  tendsto_nhds_limUnder (cauchySeq_tendsto_of_complete (F.cauchySeq_logSeq x i))

/-- **`log_F` is additive** ([Hong, Prop. 3.3.6 (1)]). -/
theorem logF_add (x y : F.Pt p) (i : Fin d) :
    F.logF (x + y) i = F.logF x i + F.logF y i := by
  obtain ⟨Nx, hNx⟩ := F.exists_bnd_pow x
  obtain ⟨Ny, hNy⟩ := F.exists_bnd_pow y
  set N := max Nx Ny
  have hbx : ∀ n, N ≤ n → F.Bnd ((p ^ n) • x) (np p ^ (n - N + 1)) := fun n hn =>
    F.bnd_mono (hNx n (le_trans (le_max_left _ _) hn))
      (pow_le_pow_of_le_one np_pos.le np_lt_one.le (by omega))
  have hby : ∀ n, N ≤ n → F.Bnd ((p ^ n) • y) (np p ^ (n - N + 1)) := fun n hn =>
    F.bnd_mono (hNy n (le_trans (le_max_right _ _) hn))
      (pow_le_pow_of_le_one np_pos.le np_lt_one.le (by omega))
  have hdiff : Tendsto (fun n => F.logSeq (x + y) i n - F.logSeq x i n - F.logSeq y i n)
      atTop (𝓝 0) := by
    have hgeo : Tendsto (fun n : ℕ => np p ^ (n - N + 1) * np p ^ (n - N + 1) / np p ^ n)
        atTop (𝓝 0) := by
      have h1 : ∀ n, N ≤ n → np p ^ (n - N + 1) * np p ^ (n - N + 1) / np p ^ n =
          (np p ^ 2 / np p ^ N) * np p ^ (n - N) := by
        intro n hn
        obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
        rw [Nat.add_sub_cancel_left]
        have hp0 := np_pos (p := p)
        field_simp
        ring
      rw [← tendsto_add_atTop_iff_nat N]
      have h2 : Tendsto (fun k : ℕ => (np p ^ 2 / np p ^ N) * np p ^ k) atTop (𝓝 0) := by
        rw [← mul_zero (np p ^ 2 / np p ^ N)]
        exact (tendsto_pow_atTop_nhds_zero_of_lt_one np_pos.le np_lt_one).const_mul _
      refine h2.congr fun k => ?_
      rw [h1 (k + N) (by omega), Nat.add_sub_cancel]
    refine squeeze_zero_norm' ?_ hgeo
    filter_upwards [eventually_ge_atTop N] with n hn
    have e : F.logSeq (x + y) i n - F.logSeq x i n - F.logSeq y i n =
        (((((p ^ n) • x + (p ^ n) • y).1 i : OC p) : ℂ_[p]) - ((p ^ n) • x).1 i -
          ((p ^ n) • y).1 i) / (p : ℂ_[p]) ^ n := by
      rw [logSeq, logSeq, logSeq, nsmul_add]
      ring
    rw [e, norm_div, norm_pow]
    have hs0 : 0 ≤ np p ^ (n - N + 1) := pow_nonneg np_pos.le _
    have hs1 : np p ^ (n - N + 1) ≤ 1 := pow_le_one₀ np_pos.le np_lt_one.le
    have h := F.norm_add_sub_le hs0 hs1 (hbx n hn) (hby n hn) i
    rw [sq] at h
    exact div_le_div_of_nonneg_right h (pow_nonneg (norm_nonneg _) _)
  have hsum : Tendsto (fun n => F.logSeq (x + y) i n) atTop
      (𝓝 (F.logF x i + F.logF y i + 0)) := by
    refine ((F.tendsto_logSeq x i).add (F.tendsto_logSeq y i)).add hdiff |>.congr fun n => ?_
    ring
  rw [add_zero] at hsum
  exact tendsto_nhds_unique (F.tendsto_logSeq (x + y) i) hsum

end FGL

end PadicHodge
