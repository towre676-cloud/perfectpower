import PerfectPower.MetricJetRealization
namespace PerfectPower.MetricJetConnection
open RiemannianEnergy MetricJetRealization
noncomputable section

def gram (g : Metric ℝ) (j k : Fin 2) :=
  if j=0 then (if k=0 then g.a else g.b) else (if k=0 then g.b else g.c)
def D (dx dy : Metric ℝ) (i j k : Fin 2) := gram (if i=0 then dx else dy) j k

def actualD (g dx dy : Metric ℝ) (i j k : Fin 2) :=
  deriv (fun t : ℝ => gram (field g dx dy (if i=0 then (t,0) else (0,t))) j k) 0

theorem derivative_interpretation (g dx dy : Metric ℝ) : actualD g dx dy = D dx dy := by
  funext i j k
  fin_cases i <;> fin_cases j <;> fin_cases k
  · exact (x_derivatives g dx dy).1.deriv
  · exact (x_derivatives g dx dy).2.1.deriv
  · exact (x_derivatives g dx dy).2.1.deriv
  · exact (x_derivatives g dx dy).2.2.deriv
  · exact (y_derivatives g dx dy).1.deriv
  · exact (y_derivatives g dx dy).2.1.deriv
  · exact (y_derivatives g dx dy).2.1.deriv
  · exact (y_derivatives g dx dy).2.2.deriv

theorem D_symmetric (dx dy : Metric ℝ) (i j k : Fin 2) : D dx dy i j k = D dx dy i k j := by
  fin_cases j <;> fin_cases k <;> simp [D,gram]

def raised (g : Metric ℝ) (l0 l1 : ℝ) : ℝ × ℝ :=
  ((g.c*l0-g.b*l1)/g.det,(-g.b*l0+g.a*l1)/g.det)

theorem raised_solves (g : Metric ℝ) (hd : g.det ≠ 0) (l0 l1 : ℝ) :
    g.a*(raised g l0 l1).1+g.b*(raised g l0 l1).2 = l0 ∧
    g.b*(raised g l0 l1).1+g.c*(raised g l0 l1).2 = l1 := by
  unfold raised
  constructor <;> field_simp [hd] <;> unfold Metric.det <;> ring

def gamma (g dx dy : Metric ℝ) (i j k : Fin 2) :=
  let l := raised g (koszul (D dx dy) i j 0) (koszul (D dx dy) i j 1)
  if k=0 then l.1 else l.2

theorem gamma_lowered (g dx dy : Metric ℝ) (hg : g.Positive) (i j k : Fin 2) :
    gram g k 0*gamma g dx dy i j 0+gram g k 1*gamma g dx dy i j 1 = koszul (actualD g dx dy) i j k := by
  rw [derivative_interpretation]
  have hs := raised_solves g (ne_of_gt hg.2) (koszul (D dx dy) i j 0) (koszul (D dx dy) i j 1)
  fin_cases k
  · simpa [gram,gamma] using hs.1
  · simpa [gram,gamma] using hs.2

theorem gamma_torsion (g dx dy : Metric ℝ) (i j k : Fin 2) : gamma g dx dy i j k = gamma g dx dy j i k := by
  unfold gamma
  rw [koszul_torsion (D dx dy) (D_symmetric dx dy) i j 0,
      koszul_torsion (D dx dy) (D_symmetric dx dy) i j 1]

theorem gamma_compatible (g dx dy : Metric ℝ) (hg : g.Positive) (i j k : Fin 2) :
    (gram g k 0*gamma g dx dy i j 0+gram g k 1*gamma g dx dy i j 1)+
    (gram g j 0*gamma g dx dy i k 0+gram g j 1*gamma g dx dy i k 1) = actualD g dx dy i j k := by
  rw [gamma_lowered g dx dy hg,gamma_lowered g dx dy hg,derivative_interpretation]
  exact koszul_compatible (D dx dy) (D_symmetric dx dy) i j k

theorem gamma_field_smooth (g dx dy : Metric ℝ) (p : ℝ × ℝ)
    (hp : (field g dx dy p).Positive) (i j k : Fin 2) :
    ContDiffAt ℝ ⊤ (fun q => gamma (field g dx dy q) dx dy i j k) p := by
  have ha := (field_smooth_a g dx dy).contDiffAt (x := p)
  have hb := (field_smooth_b g dx dy).contDiffAt (x := p)
  have hc := (field_smooth_c g dx dy).contDiffAt (x := p)
  have hd : ContDiffAt ℝ ⊤ (fun q => (field g dx dy q).det) p := by
    unfold Metric.det; fun_prop
  unfold gamma raised
  split_ifs
  · exact ((hc.mul contDiffAt_const).sub (hb.mul contDiffAt_const)).div hd (ne_of_gt hp.2)
  · exact (((hb.neg).mul contDiffAt_const).add (ha.mul contDiffAt_const)).div hd (ne_of_gt hp.2)

#print axioms derivative_interpretation
#print axioms gamma_compatible
#print axioms gamma_field_smooth
end
end PerfectPower.MetricJetConnection
