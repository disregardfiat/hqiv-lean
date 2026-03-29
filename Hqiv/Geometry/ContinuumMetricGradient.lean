import Hqiv.Geometry.ContinuumSpacetimeChart
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Metric-raised gradients on the `Fin 4` chart (sketch layer)

`ContinuumSpacetimeChart` uses the **Euclidean** `l²` inner product, so `coordsGradientComponents` is
the Riemannian gradient in that metric. This file adds **signature-agnostic coordinate partials**
`partialComponents` and **contravariant** gradients `(∇φ)^ν = g^{νμ} ∂_μ φ` built from a user-supplied
inverse metric `gInv`.

**Bridges**
* **Euclidean inverse metric** `euclideanInv = δ^{νμ}`: `contravariantGradientComponents euclideanInv`
  agrees with `coordsGradientComponents` (same as `partialComponents` componentwise) under
  `DifferentiableAt` for the pulled-back scalar.
* **Flat Minkowski** `flatMinkowskiInv = η^{νμ}` with `diag(-1,1,1,1)` in index order `0,1,2,3`:
  time component picks up a **minus** relative to `partialComponents`; this does **not** match the
  Euclidean chart gradient on the `0` index — see `contravariantGradientComponents_flatMinkowskiInv_apply`.

**Position-dependent inverse metric:** `contravariantGradientComponentsAt gInv` instantiates
`gInv` at the basepoint `c`.

**Divergence:** `coordPartialDivergence` is `∂_μ J^μ` (contravariant components in the chart).

* **Constant `g`:** `coordCovariantDivergence_constDet` is \((1/\sqrt{|g|})\sum_\mu \partial_\mu(\sqrt{|g|}\,J^\mu)\)
  for fixed `Matrix`; it agrees with `coordPartialDivergence` under differentiability, see
  `coordCovariantDivergence_constDet_eq_coordPartialDivergence`.

* **Position-dependent `g(x)`:** `coordCovariantDivergence` uses `√|g(x)|` as a scalar field on the chart;
  no shortcut to `coordPartialDivergence` without extra hypotheses (product rule in each `μ`).
  When `g` is constant as a function of coordinates, `coordCovariantDivergence_of_const_metric` recovers
  `coordCovariantDivergence_constDet`.
-/

namespace Hqiv.Geometry

noncomputable section

open scoped BigOperators Gradient
open EuclideanSpace InnerProductSpace

/-- Coordinate partial `∂_μ φ(c)` as a directional derivative along `EuclideanSpace.single μ 1` on
    `SpacetimeEuclidean4`, matching the tangent vectors used in `spacetimeCoordDivergence`. -/
noncomputable def partialComponents (φ : (Fin 4 → ℝ) → ℝ) (c : Fin 4 → ℝ) (μ : Fin 4) : ℝ :=
  fderiv ℝ (fun x : SpacetimeEuclidean4 => φ (spacetimeCoordsEquiv x)) (spacetimeOfCoords c)
    (EuclideanSpace.single μ (1 : ℝ))

/-- Contravariant gradient `(∇φ)^ν = ∑_μ g^{νμ} ∂_μ φ` at `c` (inverse metric `gInv` in coordinates). -/
noncomputable def contravariantGradientComponents (gInv : Fin 4 → Fin 4 → ℝ) (φ : (Fin 4 → ℝ) → ℝ)
    (c : Fin 4 → ℝ) : Fin 4 → ℝ :=
  fun ν => ∑ μ : Fin 4, gInv ν μ * partialComponents φ c μ

/-- Inverse metric evaluated at the chart point, e.g. lapse data `gInv (Φ, φ, t)` packaged as a map
    on coordinates. -/
noncomputable def contravariantGradientComponentsAt (gInvAt : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℝ)
    (φ : (Fin 4 → ℝ) → ℝ) (c : Fin 4 → ℝ) : Fin 4 → ℝ :=
  contravariantGradientComponents (gInvAt c) φ c

/-- Euclidean inverse metric `δ^{νμ}` (identity in the chart basis). -/
noncomputable def euclideanInv (ν μ : Fin 4) : ℝ :=
  if _ : ν = μ then (1 : ℝ) else 0

/-- Flat Minkowski inverse metric `η^{νμ}` with signature `(-,+,+,+)` and index order `0=t,1..3=x`. -/
noncomputable def flatMinkowskiInv (ν μ : Fin 4) : ℝ :=
  if _ : ν = μ then (if ν = (0 : Fin 4) then (-1 : ℝ) else (1 : ℝ)) else 0

theorem spacetimeCoordsEquiv_eq_inner_single (v : SpacetimeEuclidean4) (μ : Fin 4) :
    spacetimeCoordsEquiv v μ = inner ℝ v (EuclideanSpace.single μ (1 : ℝ)) := by
  have hinner : inner ℝ v (EuclideanSpace.single μ (1 : ℝ)) = v μ := by
    rw [PiLp.inner_apply]
    rw [Finset.sum_eq_single μ]
    · rw [EuclideanSpace.single_apply]
      simp [RCLike.inner_apply]
    · intro j _ hj
      rw [EuclideanSpace.single_apply]
      simp [hj]
    · simp
  rw [hinner]
  simp [spacetimeCoordsEquiv, PiLp.continuousLinearEquiv]

theorem partialComponents_eq_coordsGradientComponents (φ : (Fin 4 → ℝ) → ℝ) (c : Fin 4 → ℝ)
    (h : DifferentiableAt ℝ (fun x : SpacetimeEuclidean4 => φ (spacetimeCoordsEquiv x))
      (spacetimeOfCoords c)) :
    (fun μ : Fin 4 => partialComponents φ c μ) = coordsGradientComponents φ c := by
  funext μ
  unfold partialComponents coordsGradientComponents coordsGradient spacetimeGradient
  let f := fun x : SpacetimeEuclidean4 => φ (spacetimeCoordsEquiv x)
  let x := spacetimeOfCoords c
  calc
    fderiv ℝ f x (EuclideanSpace.single μ (1 : ℝ))
        = inner ℝ (gradient f x) (EuclideanSpace.single μ (1 : ℝ)) := (inner_gradient_left h).symm
    _ = spacetimeCoordsEquiv (gradient f x) μ := (spacetimeCoordsEquiv_eq_inner_single (gradient f x) μ).symm

theorem contravariantGradientComponents_euclideanInv_eq (φ : (Fin 4 → ℝ) → ℝ) (c : Fin 4 → ℝ)
    (h : DifferentiableAt ℝ (fun x : SpacetimeEuclidean4 => φ (spacetimeCoordsEquiv x))
      (spacetimeOfCoords c)) :
    contravariantGradientComponents euclideanInv φ c = coordsGradientComponents φ c := by
  funext ν
  simp only [contravariantGradientComponents, euclideanInv, partialComponents_eq_coordsGradientComponents φ c h]
  rw [Finset.sum_eq_single ν]
  · simp
  · intro μ _ hμ
    simp [Ne.symm hμ]
  · simp

theorem contravariantGradientComponentsAt_euclideanInv_eq_coordsGradientComponents
    (gInvAt : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℝ) (φ : (Fin 4 → ℝ) → ℝ) (c : Fin 4 → ℝ)
    (h : DifferentiableAt ℝ (fun x : SpacetimeEuclidean4 => φ (spacetimeCoordsEquiv x))
      (spacetimeOfCoords c)) (hg : gInvAt c = euclideanInv) :
    contravariantGradientComponentsAt gInvAt φ c = coordsGradientComponents φ c := by
  simp [contravariantGradientComponentsAt, hg, contravariantGradientComponents_euclideanInv_eq φ c h]

theorem contravariantGradientComponents_flatMinkowskiInv_apply (φ : (Fin 4 → ℝ) → ℝ) (c : Fin 4 → ℝ)
    (ν : Fin 4) :
    contravariantGradientComponents flatMinkowskiInv φ c ν =
      (if ν = (0 : Fin 4) then -1 else 1) * partialComponents φ c ν := by
  simp only [contravariantGradientComponents, flatMinkowskiInv]
  rw [Finset.sum_eq_single ν]
  · simp
  · intro μ _ hμ
    simp [Ne.symm hμ]
  · simp

/-- Coordinate divergence `∂_μ J^μ` at `c` (contravariant `J^μ` as a field on the chart). -/
noncomputable def coordPartialDivergence (J : (Fin 4 → ℝ) → Fin 4 → ℝ) (c : Fin 4 → ℝ) : ℝ :=
  ∑ μ : Fin 4, partialComponents (fun p => J p μ) c μ

theorem partialComponents_const_mul (r : ℝ) (φ : (Fin 4 → ℝ) → ℝ) (c : Fin 4 → ℝ) (μ : Fin 4)
    (h : DifferentiableAt ℝ (fun x : SpacetimeEuclidean4 => φ (spacetimeCoordsEquiv x))
      (spacetimeOfCoords c)) :
    partialComponents (fun p => r * φ p) c μ = r * partialComponents φ c μ := by
  unfold partialComponents
  rw [fderiv_const_mul h, ContinuousLinearMap.smul_apply]
  simp [smul_eq_mul]

/-- `∇_μ J^μ` in coordinates with covariant determinant weight, for **fixed** `g` (constant on the chart). -/
noncomputable def coordCovariantDivergence_constDet (g : Matrix (Fin 4) (Fin 4) ℝ) (_hg : g.det ≠ 0)
    (J : (Fin 4 → ℝ) → Fin 4 → ℝ) (c : Fin 4 → ℝ) : ℝ :=
  let vol := Real.sqrt (abs g.det)
  (1 / vol) * ∑ μ : Fin 4, partialComponents (fun p => vol * J p μ) c μ

theorem coordCovariantDivergence_constDet_eq_coordPartialDivergence (g : Matrix (Fin 4) (Fin 4) ℝ)
    (hg : g.det ≠ 0) (J : (Fin 4 → ℝ) → Fin 4 → ℝ) (c : Fin 4 → ℝ)
    (hJ : ∀ μ : Fin 4,
      DifferentiableAt ℝ (fun x : SpacetimeEuclidean4 => J (spacetimeCoordsEquiv x) μ)
        (spacetimeOfCoords c)) :
    coordCovariantDivergence_constDet g hg J c = coordPartialDivergence J c := by
  let vol := Real.sqrt (abs g.det)
  have hvol : vol ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr (abs_pos.mpr hg))
  have eqsum :
      ∑ μ : Fin 4, partialComponents (fun p => vol * J p μ) c μ =
        vol * ∑ μ : Fin 4, partialComponents (fun p => J p μ) c μ := by
    calc
      ∑ μ : Fin 4, partialComponents (fun p => vol * J p μ) c μ
          = ∑ μ : Fin 4, vol * partialComponents (fun p => J p μ) c μ := by
            refine Finset.sum_congr rfl ?_
            intro μ _
            rw [partialComponents_const_mul vol (fun p => J p μ) c μ (hJ μ)]
      _ = vol * ∑ μ : Fin 4, partialComponents (fun p => J p μ) c μ := by
            rw [← Finset.mul_sum]
  have hL : coordCovariantDivergence_constDet g hg J c =
      (1 / vol) * ∑ μ : Fin 4, partialComponents (fun p => vol * J p μ) c μ := by
    simp [coordCovariantDivergence_constDet, vol]
  rw [hL, eqsum]
  unfold coordPartialDivergence
  field_simp [hvol]

/-- Covariant divergence `∇_μ J^μ` in coordinates with `g_{μν}(x)` non-degenerate everywhere on the chart:
    `(1/√|g|) ∂_μ (√|g| J^μ)` evaluated at `c`, using the same `partialComponents` as `coordPartialDivergence`. -/
noncomputable def coordCovariantDivergence (g : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ)
    (_hg : ∀ x : Fin 4 → ℝ, (g x).det ≠ 0) (J : (Fin 4 → ℝ) → Fin 4 → ℝ) (c : Fin 4 → ℝ) : ℝ :=
  let vol (x : Fin 4 → ℝ) := Real.sqrt (abs (g x).det)
  (1 / vol c) * ∑ μ : Fin 4, partialComponents (fun p => vol p * J p μ) c μ

theorem coordCovariantDivergence_of_const_metric (g0 : Matrix (Fin 4) (Fin 4) ℝ) (hg : g0.det ≠ 0)
    (J : (Fin 4 → ℝ) → Fin 4 → ℝ) (c : Fin 4 → ℝ) :
    coordCovariantDivergence (fun _ : Fin 4 → ℝ => g0) (fun _ => hg) J c =
      coordCovariantDivergence_constDet g0 hg J c := by
  unfold coordCovariantDivergence coordCovariantDivergence_constDet
  simp

end

end Hqiv.Geometry
