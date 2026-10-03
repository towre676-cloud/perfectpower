"""Generate spark_pilot/selective/p.adb from the unmodified AdaCore QA31-008 p.adb (run: python3 spark_pilot/gen_selective.py spark_pilot/selective/p.adb)."""
import sys
from pathlib import Path
UP = Path(__file__).resolve().parents[1] / 'why3_isqrt/upstream/AdaCore__spark2014/testsuite/gnatprove/tests/QA31-008__von_neumann_sqrt'
src=(UP / 'p.adb').read_text()
head,rest=src.split('   function Sqrt_Von_Neumann',1)
tail='\nend P;\n'
def tab(f): return "\n".join(f"         when {i} => {f(i)}," for i in range(1,17))
step_cases=[]
left_cases=[]
for i in range(1,17):
    c=2**(32-2*i); s=32-2*i
    step_cases.append(f'''         when {i} =>
            pragma Assert (M_Of (I) = {c});
            pragma Assert ((Y or {c}) = Y + {c});
            pragma Assert ((Y / 2 or {c}) = Y / 2 + {c});''')
    left_cases.append(f'''         when {i} =>
            pragma Assert (M_Of (I) = {c} and then Integer (32 - 2 * I) = {s});
            pragma Assert (2 ** Integer (I) = {2**i});
            pragma Assert (Shift_Right (U64 (X), {s}) = U64 (X) / {c});
            pragma Assert (Shift_Right (Y, {s}) = Y / {c});
            pragma Assert (Shift_Right (UX, {s}) = UX / {c});''')
fn = f'''   --  Selective arithmetic support (PerfectPower pilot).  The 16 values of M are a table, the
   --  partial root is a ghost Big integer RB with Y = RB * M, UX = X - RB * RB * M and
   --  X < (RB + 1) * (RB + 1) * M, and the two lemmas below are discharged row by row with
   --  literal constants.  The original invariants and contract are unchanged.

   subtype U64 is Interfaces.Unsigned_64;

   function M_Of (I : U64) return U64 is
     (case I is
{tab(lambda i: 2**(32-2*i))}
         when others => 0)
   with Ghost;

   function R_Of (I : U64) return Big is
     (case I is
{tab(lambda i: 2**i)}
         when others => 0)
   with Ghost;

   --  One iteration of the loop body, from the state at the top (M = M_Of (I)).
   procedure Lemma_Step (X : Big; Y, UX : U64; RB : Big; I : U64)
     with Ghost,
          Pre  => I in 1 .. 16 and then X in 0 .. 2 ** 31 - 1
            and then RB in 0 .. R_Of (I) / 2 - 1
            and then Big (Y) = 4 * RB * Big (M_Of (I))
            and then Big (UX) = X - 4 * RB * RB * Big (M_Of (I))
            and then X < 4 * (RB + 1) * (RB + 1) * Big (M_Of (I)),
          Post => Big (Y or M_Of (I)) = (4 * RB + 1) * Big (M_Of (I))
            and then Big (Y / 2) = 2 * RB * Big (M_Of (I))
            and then Big ((Y / 2) or M_Of (I)) = (2 * RB + 1) * Big (M_Of (I))
            and then (if UX >= (Y or M_Of (I)) then
                        Big (UX - (Y or M_Of (I))) = X - (2 * RB + 1) * (2 * RB + 1) * Big (M_Of (I))
                        and then (2 * RB + 1) * (2 * RB + 1) * Big (M_Of (I)) <= X
                        and then X < (2 * RB + 2) * (2 * RB + 2) * Big (M_Of (I))
                      else
                        Big (UX) = X - (2 * RB) * (2 * RB) * Big (M_Of (I))
                        and then X < (2 * RB + 1) * (2 * RB + 1) * Big (M_Of (I)));

   procedure Lemma_Step (X : Big; Y, UX : U64; RB : Big; I : U64) is
   begin
      case I is
{chr(10).join(step_cases)}
         when others => null;
      end case;
   end Lemma_Step;

   --  The original shift invariants, from the algebraic ones.
   procedure Lemma_Left (X : Big; Y, UX : U64; RB : Big; I : U64)
     with Ghost,
          Pre  => I in 1 .. 16 and then X in 0 .. 2 ** 31 - 1
            and then RB in 0 .. R_Of (I) - 1
            and then Big (Y) = RB * Big (M_Of (I))
            and then Big (UX) = X - RB * RB * Big (M_Of (I))
            and then RB * RB * Big (M_Of (I)) <= X
            and then X < (RB + 1) * (RB + 1) * Big (M_Of (I)),
          Post => M_Of (I) = 2 ** Integer (32 - 2 * I)
            and then Y mod M_Of (I) = 0
            and then UX mod M_Of (I) = U64 (X) mod M_Of (I)
            and then Big (Shift_Right (Y, Integer (32 - 2 * I))) = RB
            and then Shift_Right (Y, Integer (32 - 2 * I)) < 2 ** Integer (I)
            and then Shift_Right (UX, Integer (32 - 2 * I))
                       = Shift_Right (U64 (X), Integer (32 - 2 * I))
                         - Shift_Right (Y, Integer (32 - 2 * I)) * Shift_Right (Y, Integer (32 - 2 * I))
            and then Shift_Right (Y, Integer (32 - 2 * I)) * Shift_Right (Y, Integer (32 - 2 * I))
                       <= Shift_Right (U64 (X), Integer (32 - 2 * I))
            and then (Shift_Right (Y, Integer (32 - 2 * I)) + 1) * (Shift_Right (Y, Integer (32 - 2 * I)) + 1)
                       > Shift_Right (U64 (X), Integer (32 - 2 * I));

   procedure Lemma_Left (X : Big; Y, UX : U64; RB : Big; I : U64) is
   begin
      case I is
{chr(10).join(left_cases)}
         when others => null;
      end case;
   end Lemma_Left;

   function Sqrt_Von_Neumann (X : in Sqrt_Domain) return Sqrt_Range is
      use type Interfaces.Unsigned_64;
      UX, M, Y, B : U64;

      --  Ghost entities:

      I  : U64 := 0 with Ghost;
      RB : Big := 0 with Ghost;

   begin
      UX := U64 (X);
      pragma Assert (UX <= 2 ** 31 - 1);
      M  := 16#4000_0000#;
      Y  := 0;

      while (M /= 0) loop
         pragma Assert (M = M_Of (I + 1));
         I := I + 1;
         Lemma_Step (Big (X), Y, UX, RB, I);
         B := Y or M;
         Y := Y / 2;
         if (UX >= B) then
            UX := UX - B;
            Y  := Y or M;
            RB := 2 * RB + 1;
         else
            RB := 2 * RB;
         end if;

         declare
            Bits    : U64 := 32 - 2 * I with Ghost;
            Left_X  : U64 := Shift_Right (U64 (X), Integer(Bits)) with Ghost;
            Left_Y  : U64 := Shift_Right (Y, Integer(Bits)) with Ghost;
            Left_UX : U64 := Shift_Right (UX, Integer(Bits)) with Ghost;
         begin
            Lemma_Left (Big (X), Y, UX, RB, I);
            pragma Loop_Invariant (I in 1 .. 16);
            pragma Loop_Invariant (M = M_Of (I));
            pragma Loop_Invariant (RB in 0 .. R_Of (I) - 1);
            pragma Loop_Invariant (Big (Y) = RB * Big (M));
            pragma Loop_Invariant (Big (UX) = Big (X) - RB * RB * Big (M));
            pragma Loop_Invariant (RB * RB * Big (M) <= Big (X));
            pragma Loop_Invariant (Big (X) < (RB + 1) * (RB + 1) * Big (M));
            pragma Loop_Invariant (M = 2 ** Integer(32 - 2 * I));
            pragma Loop_Invariant (Y mod M = 0);
            pragma Loop_Invariant (Left_Y < 2 ** Integer(I));
            pragma Loop_Invariant (UX mod M = U64 (X) mod M);
            pragma Loop_Invariant (Left_UX = Left_X - Left_Y * Left_Y);
            pragma Loop_Invariant (Left_Y * Left_Y <= Left_X);
            pragma Loop_Invariant (U64(Left_Y + 1) * U64(Left_Y + 1) > U64(Left_X));
         end;
         M := M / 4;
      end loop;

      return Sqrt_Range (Y);
   end Sqrt_Von_Neumann;
'''
open(sys.argv[1],'w').write(head+fn+tail)
