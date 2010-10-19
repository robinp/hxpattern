import Hxpat;

enum EnumA {
   EA1;
   EA2(x: Int);
   EA3(x: Int);
   EA4(a: EnumA);
   EA5(b: EnumB);
   EA6(x: Int, f: Float);
}

enum EnumB {
   EB1;
   EB2(s: String);
}

class GSwitchTest extends haxe.unit.TestCase {

   static function main() {
      var r = new haxe.unit.TestRunner();
      r.add(new GSwitchTest());
      r.run();
   }

   public function new() {
      super();
   }

   public function testHaxeSwitch1() {
      var e: Dynamic = EA1;
      var res = switch (e) {
         case EB1: 1;
         default: 0;
      };

      // fails, Haxe issue #222
      assertEquals(res, 0);
   }

   /*
   public function testHaxeSwitch2() {
      // doesn't compile, Haxe issue #224

      var e = EA1;
      var res = switch (e) {
         case EnumA.EA1: 1;
         case EnumA.EA2(x): 2;
         default: 0;
      };

      assertEquals(res, 1);
   }
   */

   public function testHaxeSwitch3() {
      var e = null;
      var res = switch (e) {
         case EA1: 1;
         default: 0;
      };

      // fails, Haxe issue (not submitted yet)
      assertEquals(res, 0);
   }

   public function testNoMultiEval() {
      var i = 0;
      var f = function () { 
         i++;
         return 5;
      };

      var res = Hxpat.gswitch(
            f(),
            //
            3 = 1,
            5 = 2,
            _ = 0
      );

      assertEquals(res, 2);
      assertEquals(i, 1);
   }

   public function testNestedEnum() {
      var on = EA4(EA5(EB2("apple")));
      var res = Hxpat.gswitch(
            on,
            //
            EA1 = 1,
            EA4(EA2(2)) = 2,
            EA4(EA5(EB2("apple"))) = 3,
            _ = 0
      );

      assertEquals(res, 3);
   }

   /*
   public function testFullEnumName() {
      // doesn't compile, haxe issue#224
      var on = EA2(5);
      var res = Hxpat.gswitch(
            on,
            //
            EnumA.EA1 = 1,
            EnumA.EA2(x) = 2,
            _ = 0
      );

      assertEquals(res, 2);
   }
   */

   public function testMixedExprType() {
      var on = 5;
      var x = 10;
      Hxpat.gswitch(
            on,
            //
            5 = {
               x = Std.random(5);
               // error, this is needed for the code to even compile
               null; 
            },
            7 = {
               new List().add(3);
            },
            _ = throw "x"
      );
      assertEquals(x != 10, true);
   }

   public function testNullSwitch() {
      var on = null;
      var res = Hxpat.gswitch(
         on,
         //
         5 = 1,
         EA1 = 2,
         _ = 0
      );

      assertEquals(res, 0);
   }

   public function testDynamic() {
      var on : Dynamic = EA2(5);

      var res = Hxpat.gswitch(
         on,
         //
         EB2(s) = 1,
         EB1 =    2,
         EA2(x) & EA3(x) = 3,
         EA1 =    4,
         _ = 0
      );

      assertEquals(res, 3);
   } 
 
   public function testDynamicShortName() {
      var on : Dynamic = EA2(5);

      var res = Hxpat.gswitch(
         on,
         //
         EB2(s) = 1,
         EB1 =    2,
         EA2(x) = 3,
         EA1 =    4,
         _ = 0
      );

      assertEquals(res, 3);
   }


   public function testDefault() { 
      var on = EA2(7);
      var res = Hxpat.gswitch(
            on,
            //
            EA1 = 1,
            EA4(EA2(2)) = 2,
            EA4(EA5(EB2("apple"))) = 3,
            _ = 0
      );

      assertEquals(res, 0);
   }

   public function testReturn() {
      var f = function() {
         return Hxpat.gswitch(
               EA1,
               //
               EA1 =
                  return 10,
               EA2(_) = 2,
               _ = 0
         );
      };

      assertEquals(f(), 10);
   }

   public function testVarNestedEnum() {
      var s = "apple";

      var res = Hxpat.gswitch(
            EB2("apple"),
            //
            EB2(!s) = 1,
            _ = 0
      );

      assertEquals(res, 1);
   }

   public function testMultiCase() {
      var res = Hxpat.gswitch(
            EA2(5),
            //
            EA3(y) & EA2(y) = 1,
            _ = 0
      );

      assertEquals(res, 1);
   } 
 
   public function testMultiCaseGuard() {
      var res = Hxpat.gswitch(
            EA2(5),
            //
            EA3(y) & EA2(y) | (y > 5) = 1,
            _ = 0
      );

      assertEquals(res, 0);
   }


   public function testGuard1() { 
      var res = Hxpat.gswitch(
            EA6(5, 10.0),
            //
            EA3(x) = 1,
            EA6(a, b) | (a > 3 && b > 15.0) = 2,
            EA6(a, b) | (a > 3 && b == 10.0) = 3,
            _ = 0
      );

      assertEquals(res, 3);
   }

   public function testComplex1() {
      var v = 5;

      var res = Hxpat.gswitch(
            EA4(EA4(EA6(5, 10.0))),
            //
            EA4(EA4(x)) =
               Hxpat.gswitch(
                  x,
                  //
                  EA6(!v, b) | (b < 15.0) = 1,
                  _ = 0
               ),
            _ = 0
      );

      assertEquals(res, 1);
   }
}
