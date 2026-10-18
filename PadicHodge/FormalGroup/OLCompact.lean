/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.FormalGroup.OK
import PadicHodge.GroupScheme.SerreTateCompact
import Mathlib.NumberTheory.Padics.ProperSpace

/-!
# `O_L` is compact

For a finite extension `L/ℚ_p` inside `ℚ̄_p`, the unit ball `{z ∈ L | |z| ≤ 1}` of the image of `L`
in `ℂ_p` is compact (`OL.isCompact_unitBall`: `L` is a finite-dimensional, hence proper, normed
`ℚ_p`-space), so `O_L = OLSub L` with the subspace topology of `O_{ℂ_p}` is a compact space
(`OL.compactSpace_OLSub`). This is the compact companion topology of `OL L` (which itself
carries the discrete uniformity) needed for the compactness argument in the essential
surjectivity of Serre–Tate over `O_L` (the analogue of `ℤ_p^{ℕ^σ}` in
`GroupScheme/SerreTateCompact.lean`).

**`OL.instCoeffRing`**: `O_L` is a coefficient ring for Serre–Tate (`SerreTate.CoeffRing`), with
uniformiser `OL.uniformizer L` and this compact companion topology (the cosets of `𝔪_L^w` are
closed balls of positive radius, open in the ultrametric `ℂ_p`); `O_L` is a domain
(`OL.instIsDomain`) and a principal ideal ring (`OL.instIsPrincipalIdealRing`).
-/

noncomputable section

namespace PadicHodge

namespace OL

variable {p : ℕ} [hp : Fact p.Prime] (L : IntermediateField ℚ_[p] (PadicAlgCl p))
  [FiniteDimensional ℚ_[p] L]

/-- **The unit ball of `L ⊆ ℂ_p` is compact.** -/
theorem isCompact_unitBall : IsCompact {z : ℂ_[p] | z ∈ cpSubmodule L ∧ ‖z‖ ≤ 1} := by
  haveI : ProperSpace (cpSubmodule L) := FiniteDimensional.proper ℚ_[p] (cpSubmodule L)
  have hc := (isCompact_closedBall (0 : cpSubmodule L) 1).image continuous_subtype_val
  convert hc using 1
  ext z
  constructor
  · rintro ⟨hz, h1⟩
    refine ⟨⟨z, hz⟩, ?_, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    exact h1
  · rintro ⟨w, hw, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right] at hw
    exact ⟨w.2, hw⟩

/-- **`O_L` is compact** for the subspace topology of `O_{ℂ_p} ⊆ ℂ_p`. -/
instance compactSpace_OLSub : CompactSpace (OLSub L) := by
  rw [← isCompact_univ_iff]
  have hemb : Topology.IsEmbedding (fun x : OLSub L => ((x : OC p) : ℂ_[p])) :=
    Topology.IsEmbedding.subtypeVal.comp Topology.IsEmbedding.subtypeVal
  rw [hemb.isCompact_iff, Set.image_univ]
  convert isCompact_unitBall L using 1
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x.2, norm_OC_le _⟩
  · rintro ⟨hz, h1⟩
    exact ⟨⟨⟨z, mem_OC.mpr h1⟩, hz⟩, rfl⟩

/-- `O_L` is a domain. -/
instance instIsDomain : IsDomain (OL L) := inferInstanceAs (IsDomain (OLSub L))

/-- **`O_L` is a coefficient ring for Serre–Tate.** -/
instance instCoeffRing : SerreTate.CoeffRing (OL L) where
  uniformizer := uniformizer L
  uniformizer_ne_zero := uniformizer_ne_zero
  maximalIdeal_eq := maximalIdeal_eq
  cptTop := (inferInstance : TopologicalSpace (OLSub L))
  compactSpace := compactSpace_OLSub L
  isOpen_coset w c := by
    have e : ∀ x : OLSub L, ((show OL L from x) - c ∈ IsLocalRing.maximalIdeal (OL L) ^ w ↔
        ((x : OC p) : ℂ_[p]) ∈
          Metric.closedBall ((toOC c : OC p) : ℂ_[p]) (nrm (uniformizer L) ^ w)) := fun x => by
      rw [maximalIdeal_eq, mem_span_pow_iff, Metric.mem_closedBall, dist_eq_norm, nrm, map_sub,
        AddSubgroupClass.coe_sub]
      rfl
    have h :
        IsOpen {x : OLSub L | (show OL L from x) - c ∈ IsLocalRing.maximalIdeal (OL L) ^ w} := by
      rw [show {x : OLSub L | (show OL L from x) - c ∈ IsLocalRing.maximalIdeal (OL L) ^ w} =
        (fun x : OLSub L => ((x : OC p) : ℂ_[p])) ⁻¹'
          Metric.closedBall ((toOC c : OC p) : ℂ_[p]) (nrm (uniformizer L) ^ w) from Set.ext e]
      exact (IsUltrametricDist.isOpen_closedBall _
        (pow_pos (nrm_pos uniformizer_ne_zero) w).ne').preimage
        (continuous_subtype_val.comp continuous_subtype_val)
    exact h

/-- `O_L` is a principal ideal ring (a discrete valuation ring,
`SerreTate.isDiscreteValuationRing`). -/
instance instIsPrincipalIdealRing : IsPrincipalIdealRing (OL L) :=
  (SerreTate.isDiscreteValuationRing (R := OL L)).toIsPrincipalIdealRing

end OL

end PadicHodge
