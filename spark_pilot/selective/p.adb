with Interfaces; use Interfaces;

package body P
  with SPARK_Mode => On
is
   -----------------
   -- Sqrt_Binary --
   -----------------

   function Sqrt_Binary (X : in Sqrt_Domain) return Sqrt_Range is
      subtype Upper_Guess is Integer range 0 .. Sqrt_Range'Last + 1;
      Lower : Sqrt_Range  := 0;
      Upper : Upper_Guess := Upper_Guess'Last;
   begin
      loop
         pragma Loop_Invariant (Lower * Lower <= X);
         pragma Loop_Invariant (Big (X) < Big (Upper) * Big (Upper));
         pragma Loop_Variant (Decreases => Upper - Lower);

         exit when Lower + 1 = Upper;
         declare
            Middle : constant Sqrt_Range := (Lower + Upper) / 2;
         begin
            if Middle * Middle > X then
               Upper := Middle;
            else
               Lower := Middle;
            end if;
         end;
      end loop;

      return Lower;
   end Sqrt_Binary;

   ----------------------
   -- Sqrt_Von_Neumann --
   ----------------------

--  Algorithm from Warren'a "Hacker's Delight" Figure 11.4
--  int isqrt4(unsigned x) {
--     unsigned m, y, b;
--     m = 0x40000000;
--     y = 0;
--     while(m != 0) {              // Do 16 times.
--        b = y | m;
--        y = y >> 1;
--        if (x >= b) {
--           x = x - b;
--           y = y | m;
--        }
--        m = m >> 2;
--     }
--     return y;
--  }

   --  Selective arithmetic support (PerfectPower pilot).  The 16 values of M are a table, the
   --  partial root is a ghost Big integer RB with Y = RB * M, UX = X - RB * RB * M and
   --  X < (RB + 1) * (RB + 1) * M, and the two lemmas below are discharged row by row with
   --  literal constants.  The original invariants and contract are unchanged.

   subtype U64 is Interfaces.Unsigned_64;

   function M_Of (I : U64) return U64 is
     (case I is
         when 1 => 1073741824,
         when 2 => 268435456,
         when 3 => 67108864,
         when 4 => 16777216,
         when 5 => 4194304,
         when 6 => 1048576,
         when 7 => 262144,
         when 8 => 65536,
         when 9 => 16384,
         when 10 => 4096,
         when 11 => 1024,
         when 12 => 256,
         when 13 => 64,
         when 14 => 16,
         when 15 => 4,
         when 16 => 1,
         when others => 0)
   with Ghost;

   function R_Of (I : U64) return Big is
     (case I is
         when 1 => 2,
         when 2 => 4,
         when 3 => 8,
         when 4 => 16,
         when 5 => 32,
         when 6 => 64,
         when 7 => 128,
         when 8 => 256,
         when 9 => 512,
         when 10 => 1024,
         when 11 => 2048,
         when 12 => 4096,
         when 13 => 8192,
         when 14 => 16384,
         when 15 => 32768,
         when 16 => 65536,
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
         when 1 =>
            pragma Assert (M_Of (I) = 1073741824);
            pragma Assert ((Y or 1073741824) = Y + 1073741824);
            pragma Assert ((Y / 2 or 1073741824) = Y / 2 + 1073741824);
         when 2 =>
            pragma Assert (M_Of (I) = 268435456);
            pragma Assert ((Y or 268435456) = Y + 268435456);
            pragma Assert ((Y / 2 or 268435456) = Y / 2 + 268435456);
         when 3 =>
            pragma Assert (M_Of (I) = 67108864);
            pragma Assert ((Y or 67108864) = Y + 67108864);
            pragma Assert ((Y / 2 or 67108864) = Y / 2 + 67108864);
         when 4 =>
            pragma Assert (M_Of (I) = 16777216);
            pragma Assert ((Y or 16777216) = Y + 16777216);
            pragma Assert ((Y / 2 or 16777216) = Y / 2 + 16777216);
         when 5 =>
            pragma Assert (M_Of (I) = 4194304);
            pragma Assert ((Y or 4194304) = Y + 4194304);
            pragma Assert ((Y / 2 or 4194304) = Y / 2 + 4194304);
         when 6 =>
            pragma Assert (M_Of (I) = 1048576);
            pragma Assert ((Y or 1048576) = Y + 1048576);
            pragma Assert ((Y / 2 or 1048576) = Y / 2 + 1048576);
         when 7 =>
            pragma Assert (M_Of (I) = 262144);
            pragma Assert ((Y or 262144) = Y + 262144);
            pragma Assert ((Y / 2 or 262144) = Y / 2 + 262144);
         when 8 =>
            pragma Assert (M_Of (I) = 65536);
            pragma Assert ((Y or 65536) = Y + 65536);
            pragma Assert ((Y / 2 or 65536) = Y / 2 + 65536);
         when 9 =>
            pragma Assert (M_Of (I) = 16384);
            pragma Assert ((Y or 16384) = Y + 16384);
            pragma Assert ((Y / 2 or 16384) = Y / 2 + 16384);
         when 10 =>
            pragma Assert (M_Of (I) = 4096);
            pragma Assert ((Y or 4096) = Y + 4096);
            pragma Assert ((Y / 2 or 4096) = Y / 2 + 4096);
         when 11 =>
            pragma Assert (M_Of (I) = 1024);
            pragma Assert ((Y or 1024) = Y + 1024);
            pragma Assert ((Y / 2 or 1024) = Y / 2 + 1024);
         when 12 =>
            pragma Assert (M_Of (I) = 256);
            pragma Assert ((Y or 256) = Y + 256);
            pragma Assert ((Y / 2 or 256) = Y / 2 + 256);
         when 13 =>
            pragma Assert (M_Of (I) = 64);
            pragma Assert ((Y or 64) = Y + 64);
            pragma Assert ((Y / 2 or 64) = Y / 2 + 64);
         when 14 =>
            pragma Assert (M_Of (I) = 16);
            pragma Assert ((Y or 16) = Y + 16);
            pragma Assert ((Y / 2 or 16) = Y / 2 + 16);
         when 15 =>
            pragma Assert (M_Of (I) = 4);
            pragma Assert ((Y or 4) = Y + 4);
            pragma Assert ((Y / 2 or 4) = Y / 2 + 4);
         when 16 =>
            pragma Assert (M_Of (I) = 1);
            pragma Assert ((Y or 1) = Y + 1);
            pragma Assert ((Y / 2 or 1) = Y / 2 + 1);
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
         when 1 =>
            pragma Assert (M_Of (I) = 1073741824 and then Integer (32 - 2 * I) = 30);
            pragma Assert (2 ** Integer (I) = 2);
            pragma Assert (Shift_Right (U64 (X), 30) = U64 (X) / 1073741824);
            pragma Assert (Shift_Right (Y, 30) = Y / 1073741824);
            pragma Assert (Shift_Right (UX, 30) = UX / 1073741824);
         when 2 =>
            pragma Assert (M_Of (I) = 268435456 and then Integer (32 - 2 * I) = 28);
            pragma Assert (2 ** Integer (I) = 4);
            pragma Assert (Shift_Right (U64 (X), 28) = U64 (X) / 268435456);
            pragma Assert (Shift_Right (Y, 28) = Y / 268435456);
            pragma Assert (Shift_Right (UX, 28) = UX / 268435456);
         when 3 =>
            pragma Assert (M_Of (I) = 67108864 and then Integer (32 - 2 * I) = 26);
            pragma Assert (2 ** Integer (I) = 8);
            pragma Assert (Shift_Right (U64 (X), 26) = U64 (X) / 67108864);
            pragma Assert (Shift_Right (Y, 26) = Y / 67108864);
            pragma Assert (Shift_Right (UX, 26) = UX / 67108864);
         when 4 =>
            pragma Assert (M_Of (I) = 16777216 and then Integer (32 - 2 * I) = 24);
            pragma Assert (2 ** Integer (I) = 16);
            pragma Assert (Shift_Right (U64 (X), 24) = U64 (X) / 16777216);
            pragma Assert (Shift_Right (Y, 24) = Y / 16777216);
            pragma Assert (Shift_Right (UX, 24) = UX / 16777216);
         when 5 =>
            pragma Assert (M_Of (I) = 4194304 and then Integer (32 - 2 * I) = 22);
            pragma Assert (2 ** Integer (I) = 32);
            pragma Assert (Shift_Right (U64 (X), 22) = U64 (X) / 4194304);
            pragma Assert (Shift_Right (Y, 22) = Y / 4194304);
            pragma Assert (Shift_Right (UX, 22) = UX / 4194304);
         when 6 =>
            pragma Assert (M_Of (I) = 1048576 and then Integer (32 - 2 * I) = 20);
            pragma Assert (2 ** Integer (I) = 64);
            pragma Assert (Shift_Right (U64 (X), 20) = U64 (X) / 1048576);
            pragma Assert (Shift_Right (Y, 20) = Y / 1048576);
            pragma Assert (Shift_Right (UX, 20) = UX / 1048576);
         when 7 =>
            pragma Assert (M_Of (I) = 262144 and then Integer (32 - 2 * I) = 18);
            pragma Assert (2 ** Integer (I) = 128);
            pragma Assert (Shift_Right (U64 (X), 18) = U64 (X) / 262144);
            pragma Assert (Shift_Right (Y, 18) = Y / 262144);
            pragma Assert (Shift_Right (UX, 18) = UX / 262144);
         when 8 =>
            pragma Assert (M_Of (I) = 65536 and then Integer (32 - 2 * I) = 16);
            pragma Assert (2 ** Integer (I) = 256);
            pragma Assert (Shift_Right (U64 (X), 16) = U64 (X) / 65536);
            pragma Assert (Shift_Right (Y, 16) = Y / 65536);
            pragma Assert (Shift_Right (UX, 16) = UX / 65536);
         when 9 =>
            pragma Assert (M_Of (I) = 16384 and then Integer (32 - 2 * I) = 14);
            pragma Assert (2 ** Integer (I) = 512);
            pragma Assert (Shift_Right (U64 (X), 14) = U64 (X) / 16384);
            pragma Assert (Shift_Right (Y, 14) = Y / 16384);
            pragma Assert (Shift_Right (UX, 14) = UX / 16384);
         when 10 =>
            pragma Assert (M_Of (I) = 4096 and then Integer (32 - 2 * I) = 12);
            pragma Assert (2 ** Integer (I) = 1024);
            pragma Assert (Shift_Right (U64 (X), 12) = U64 (X) / 4096);
            pragma Assert (Shift_Right (Y, 12) = Y / 4096);
            pragma Assert (Shift_Right (UX, 12) = UX / 4096);
         when 11 =>
            pragma Assert (M_Of (I) = 1024 and then Integer (32 - 2 * I) = 10);
            pragma Assert (2 ** Integer (I) = 2048);
            pragma Assert (Shift_Right (U64 (X), 10) = U64 (X) / 1024);
            pragma Assert (Shift_Right (Y, 10) = Y / 1024);
            pragma Assert (Shift_Right (UX, 10) = UX / 1024);
         when 12 =>
            pragma Assert (M_Of (I) = 256 and then Integer (32 - 2 * I) = 8);
            pragma Assert (2 ** Integer (I) = 4096);
            pragma Assert (Shift_Right (U64 (X), 8) = U64 (X) / 256);
            pragma Assert (Shift_Right (Y, 8) = Y / 256);
            pragma Assert (Shift_Right (UX, 8) = UX / 256);
         when 13 =>
            pragma Assert (M_Of (I) = 64 and then Integer (32 - 2 * I) = 6);
            pragma Assert (2 ** Integer (I) = 8192);
            pragma Assert (Shift_Right (U64 (X), 6) = U64 (X) / 64);
            pragma Assert (Shift_Right (Y, 6) = Y / 64);
            pragma Assert (Shift_Right (UX, 6) = UX / 64);
         when 14 =>
            pragma Assert (M_Of (I) = 16 and then Integer (32 - 2 * I) = 4);
            pragma Assert (2 ** Integer (I) = 16384);
            pragma Assert (Shift_Right (U64 (X), 4) = U64 (X) / 16);
            pragma Assert (Shift_Right (Y, 4) = Y / 16);
            pragma Assert (Shift_Right (UX, 4) = UX / 16);
         when 15 =>
            pragma Assert (M_Of (I) = 4 and then Integer (32 - 2 * I) = 2);
            pragma Assert (2 ** Integer (I) = 32768);
            pragma Assert (Shift_Right (U64 (X), 2) = U64 (X) / 4);
            pragma Assert (Shift_Right (Y, 2) = Y / 4);
            pragma Assert (Shift_Right (UX, 2) = UX / 4);
         when 16 =>
            pragma Assert (M_Of (I) = 1 and then Integer (32 - 2 * I) = 0);
            pragma Assert (2 ** Integer (I) = 65536);
            pragma Assert (Shift_Right (U64 (X), 0) = U64 (X) / 1);
            pragma Assert (Shift_Right (Y, 0) = Y / 1);
            pragma Assert (Shift_Right (UX, 0) = UX / 1);
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

end P;
