import PolynomialBound
import PolynomialIntegral
open Polynomial MeasureTheory Set
open scoped ComplexConjugate
namespace RHTuckPolynomial
local notation "μI" => volume.restrict (Icc (-1:ℝ) 1)

noncomputable def mixed (p q : Polynomial ℂ) (z : ℝ × ℝ) : ℂ :=
  conj (p.eval (z.1:ℂ)) * quotient q z.1 z.2
noncomputable def form (p q : Polynomial ℂ) : ℂ :=
  ∫ z, mixed p q z ∂((μI).prod (μI))

theorem form_hermitian (p q : Polynomial ℂ) : form p q = conj (form q p) := by
  have ha : Integrable (mixed p q) ((μI).prod (μI)) := mixed_integrable p q
  have hb : Integrable (fun z => conj (mixed q p z)) ((μI).prod (μI)) :=
    Complex.conjCLE.toContinuousLinearMap.integrable_comp (mixed_integrable q p)
  have hp : (fun z => mixed p q z + mixed p q z.swap) =
      (fun z => conj (mixed q p z) + conj (mixed q p z.swap)) := by
    funext z
    simp only [mixed,quotient,Prod.fst_swap,Prod.snd_swap,abs_sub_comm z.2 z.1,
      map_mul,map_div₀,map_sub,Complex.conj_ofReal,starRingEnd_self_apply]
    ring
  have he := congrArg (fun f : ℝ × ℝ → ℂ => ∫ z, f z ∂((μI).prod (μI))) hp
  have has : Integrable (fun z => mixed p q z.swap) ((μI).prod (μI)) := ha.swap
  have hbs : Integrable (fun z => conj (mixed q p z.swap)) ((μI).prod (μI)) := hb.swap
  have hea := integral_add (f := fun z => mixed p q z) (g := fun z => mixed p q z.swap) ha has
  have heb := integral_add (f := fun z => conj (mixed q p z))
    (g := fun z => conj (mixed q p z.swap)) hb hbs
  have he := hea.symm.trans (he.trans heb)
  have hsa := integral_prod_swap (μ := μI) (ν := μI) (mixed p q)
  have hsb := integral_prod_swap (μ := μI) (ν := μI) (fun z => conj (mixed q p z))
  simp only [hsa,hsb,integral_conj] at he
  change form p q + form p q = conj (form q p) + conj (form q p) at he
  linear_combination he / 2

theorem form_eq_operator (p q : Polynomial ℂ) :
    form p q = ∫ x in Icc (-1:ℝ) 1,
      conj (p.eval (x:ℂ)) * (RHTuckLinear.operator q).eval (x:ℂ) := by
  unfold form mixed
  calc
    _ = ∫ x, ∫ y, conj (p.eval (x:ℂ)) * quotient q x y ∂μI ∂μI :=
      (integral_integral (f := fun x y : ℝ => conj (p.eval (x:ℂ)) * quotient q x y)
        (mixed_integrable p q)).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
      rw [integral_const_mul]
      congr 1
      rw [integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le (by norm_num : (-1:ℝ) ≤ 1)]
      exact integral_eq_operator q hx

theorem operator_hermitian (p q : Polynomial ℂ) :
    (∫ x in Icc (-1:ℝ) 1, conj (p.eval (x:ℂ)) * (RHTuckLinear.operator q).eval (x:ℂ)) =
    conj (∫ x in Icc (-1:ℝ) 1, conj (q.eval (x:ℂ)) * (RHTuckLinear.operator p).eval (x:ℂ)) := by
  rw [← form_eq_operator,← form_eq_operator]
  exact form_hermitian p q
end RHTuckPolynomial
