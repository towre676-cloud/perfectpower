import PerfectPower.StructuralCertificates

namespace PerfectPower.StructuralPackets

def form0 (x0 x1 : ℚ) : ℚ := ((2:ℚ)/3)*x0*x0+((8:ℚ)/3)*x0*x1+((8:ℚ)/3)*x1*x0+((326:ℚ)/21)*x1*x1

theorem ldl0 (x0 x1 : ℚ) : form0 x0 x1=((2:ℚ)/3)*(((1:ℚ))*x0+((4:ℚ))*x1)^2+((34:ℚ)/7)*(((0:ℚ))*x0+((1:ℚ))*x1)^2 := by unfold form0; ring

theorem nonnegative0 (x0 x1 : ℚ) : 0 ≤ form0 x0 x1 := by rw [ldl0]; positivity

theorem dissipation0 (x0 x1 : ℚ) : (2*((2:ℚ)/3)*x0*(((-1:ℚ))*x0+((10:ℚ))*x1)+2*((8:ℚ)/3)*x0*(((0:ℚ))*x0+((-2:ℚ))*x1)+2*((8:ℚ)/3)*x1*(((-1:ℚ))*x0+((10:ℚ))*x1)+2*((326:ℚ)/21)*x1*(((0:ℚ))*x0+((-2:ℚ))*x1))+2*((1:ℚ)/4)*form0 x0 x1=-(x0^2+x1^2) := by unfold form0; ring

def form1 (x0 x1 x2 : ℚ) : ℚ := ((127:ℚ)/385)*x0*x0+((2:ℚ)/385)*x0*x1+((-2:ℚ)/385)*x0*x2+((2:ℚ)/385)*x1*x0+((123:ℚ)/385)*x1*x1+((2:ℚ)/77)*x1*x2+((-2:ℚ)/385)*x2*x0+((2:ℚ)/77)*x2*x1+((81:ℚ)/385)*x2*x2

theorem ldl1 (x0 x1 x2 : ℚ) : form1 x0 x1 x2=((127:ℚ)/385)*(((1:ℚ))*x0+((2:ℚ)/127)*x1+((-2:ℚ)/127)*x2)^2+((2231:ℚ)/6985)*(((0:ℚ))*x0+((1:ℚ))*x1+((182:ℚ)/2231)*x2)^2+((5109:ℚ)/24541)*(((0:ℚ))*x0+((0:ℚ))*x1+((1:ℚ))*x2)^2 := by unfold form1; ring

theorem nonnegative1 (x0 x1 x2 : ℚ) : 0 ≤ form1 x0 x1 x2 := by rw [ldl1]; positivity

theorem dissipation1 (x0 x1 x2 : ℚ) : (2*((127:ℚ)/385)*x0*(((-2:ℚ))*x0+((1:ℚ))*x1+((0:ℚ))*x2)+2*((2:ℚ)/385)*x0*(((-1:ℚ))*x0+((-2:ℚ))*x1+((1:ℚ))*x2)+2*((-2:ℚ)/385)*x0*(((0:ℚ))*x0+((-1:ℚ))*x1+((-3:ℚ))*x2)+2*((2:ℚ)/385)*x1*(((-2:ℚ))*x0+((1:ℚ))*x1+((0:ℚ))*x2)+2*((123:ℚ)/385)*x1*(((-1:ℚ))*x0+((-2:ℚ))*x1+((1:ℚ))*x2)+2*((2:ℚ)/77)*x1*(((0:ℚ))*x0+((-1:ℚ))*x1+((-3:ℚ))*x2)+2*((-2:ℚ)/385)*x2*(((-2:ℚ))*x0+((1:ℚ))*x1+((0:ℚ))*x2)+2*((2:ℚ)/77)*x2*(((-1:ℚ))*x0+((-2:ℚ))*x1+((1:ℚ))*x2)+2*((81:ℚ)/385)*x2*(((0:ℚ))*x0+((-1:ℚ))*x1+((-3:ℚ))*x2))+2*((1:ℚ)/2)*form1 x0 x1 x2=-(x0^2+x1^2+x2^2) := by unfold form1; ring

def form2 (x0 x1 x2 : ℚ) : ℚ := ((1:ℚ))*x0*x0+((1:ℚ))*x0*x1+((1:ℚ))*x0*x2+((1:ℚ))*x1*x0+((1:ℚ))*x1*x1+((1:ℚ))*x1*x2+((1:ℚ))*x2*x0+((1:ℚ))*x2*x1+((1:ℚ))*x2*x2

theorem ldl2 (x0 x1 x2 : ℚ) : form2 x0 x1 x2=((1:ℚ))*(((1:ℚ))*x0+((1:ℚ))*x1+((1:ℚ))*x2)^2+((0:ℚ))*(((0:ℚ))*x0+((1:ℚ))*x1+((0:ℚ))*x2)^2+((0:ℚ))*(((0:ℚ))*x0+((0:ℚ))*x1+((1:ℚ))*x2)^2 := by unfold form2; ring

theorem nonnegative2 (x0 x1 x2 : ℚ) : 0 ≤ form2 x0 x1 x2 := by rw [ldl2]; positivity

def form3 (x0 x1 : ℚ) : ℚ := ((1:ℚ))*x0*x0+((999999999999999999999999999999:ℚ)/1000000000000000000000000000000)*x0*x1+((999999999999999999999999999999:ℚ)/1000000000000000000000000000000)*x1*x0+((1:ℚ))*x1*x1

theorem ldl3 (x0 x1 : ℚ) : form3 x0 x1=((1:ℚ))*(((1:ℚ))*x0+((999999999999999999999999999999:ℚ)/1000000000000000000000000000000)*x1)^2+((1999999999999999999999999999999:ℚ)/1000000000000000000000000000000000000000000000000000000000000)*(((0:ℚ))*x0+((1:ℚ))*x1)^2 := by unfold form3; ring

theorem nonnegative3 (x0 x1 : ℚ) : 0 ≤ form3 x0 x1 := by rw [ldl3]; positivity

def energy (v a p : ℚ) : ℚ := v^2+a^2+(2*a-1)^2+(v+4-8*a)^2+(a*v-2*a-2*p*v+1)^2+(2*a*v+4*a-4*p*v-v-2)^2

theorem global_energy (v a p : ℚ) : 1/5 ≤ energy v a p := by
  have hid : energy v a p-1/5=v^2+5*(a-2/5)^2+(v+4-8*a)^2+(a*v-2*a-2*p*v+1)^2+(2*a*v+4*a-4*p*v-v-2)^2 := by unfold energy; ring
  have hn : 0 ≤ v^2+5*(a-2/5)^2+(v+4-8*a)^2+(a*v-2*a-2*p*v+1)^2+(2*a*v+4*a-4*p*v-v-2)^2 := by positivity
  linarith

theorem slice_energy (a p : ℚ) : 22/89 ≤ energy 0 a p := by
  have hid : energy 0 a p-22/89=89*(a-44/89)^2 := by unfold energy; ring
  have hn : 0 ≤ 89*(a-44/89)^2 := by positivity
  linarith

theorem slice_attainment (p : ℚ) : energy 0 (44/89) p=22/89 := by unfold energy; ring

end PerfectPower.StructuralPackets
