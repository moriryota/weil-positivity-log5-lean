import CentralMassDensity
import RawPythagoras
open MeasureTheory Set
namespace RHCentralMass
open RHRawProjection
 theorem integral_mass {L a b r : ℝ} (u : ℝ → ℝ) (hu : MemLp u 2 volume)
    (ha : 0<a) (h2 : 2*a≤2*L) (h3 : 2*L≤3*a)
    (hW : 2*L<a+b) (hab : b<2*a) :
    (∫ x in Ico (-L) L, ((Ioo (L-b) (-L+b)).indicator (project L a r u) x)^2) =
    r^2/(2+r^2)*(∫ x in Ico (-L) L, (project L a r u x)^2) := by
  have hp := project_memLp L a r hu
  have hc := hp.indicator (s := Ioo (L-b) (-L+b)) measurableSet_Ioo
  have hip := square_integrable hp
  have hic := square_integrable hc
  have hig : Integrable (RHCentralDensity.density L a b r u) volume :=
    hic.sub (hip.const_mul _)
  have he := RHRealChain.integral_chain_decomposition
    (RHCentralDensity.density L a b r u) (-L) (2*L) a ha h2 h3 hig.integrableOn
  simp only [show -L+2*L=L by ring] at he
  have htint : (∫ t in Ico (-L) (L-2*a),
      RHCentralDensity.density L a b r u t + RHCentralDensity.density L a b r u (t+a) +
      RHCentralDensity.density L a b r u (t+2*a)) = 0 := by
    calc
      _ = ∫ _t in Ico (-L) (L-2*a), (0:ℝ) :=
        setIntegral_congr_fun measurableSet_Ico (fun t ht =>
          RHCentralDensity.triple_zero u ha h2 h3 hW hab ht)
      _ = 0 := by simp
  have hbint : (∫ t in Ico (L-2*a) (-L+a),
      RHCentralDensity.density L a b r u t + RHCentralDensity.density L a b r u (t+a)) = 0 := by
    calc
      _ = ∫ _t in Ico (L-2*a) (-L+a), (0:ℝ) :=
        setIntegral_congr_fun measurableSet_Ico (fun t ht =>
          RHCentralDensity.double_zero u ha h2 h3 ht)
      _ = 0 := by simp
  rw [htint, hbint, add_zero] at he
  dsimp only [RHCentralDensity.density] at he
  rw [integral_sub hic.integrableOn (hip.const_mul _).integrableOn,
    integral_const_mul] at he
  linarith
end RHCentralMass
