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

import GSwitch;

class GSwitchTest extends haxe.unit.TestCase {

   static function main() {
      var r = new haxe.unit.TestRunner();
      r.add(new GSwitchTest());
      r.run();
   }

   public function new() {
      super();
   }

   public function testNoMultiEval() {
      var i = 0;
      var f = function () { 
         i++;
         return 5;
      };

      var res = GSwitch.guarded(switch (f()) {
            case 3: 1;
            case 5: 2;
            default: 0;
      });

      assertEquals(res, 2);
      assertEquals(i, 1);
   }

   public function testGuardedEnum() {
      var on = EA4(EA5(EB2("apple")));
      var res = GSwitch.guarded(switch (on) {
            case EA1: 1;
            case EA4(EA2(2)): 2;
            case EA4(EA5(EB2("apple"))): 3;
            default: 0;
      });

      assertEquals(res, 3);
   }

   public function testDefault() { 
      var on = EA2(7);
      var res = GSwitch.guarded(switch (on) {
            case EA1: 1;
            case EA4(EA2(2)): 2;
            case EA4(EA5(EB2("apple"))): 3;
            default: 0;
      });

      assertEquals(res, 0);
   }

   public function testReturn() {
      var f = function() {
         return GSwitch.guarded(switch (EA1) {
               case EA1:
                  return 10;
               case EA2(_): 2;
               default: 0;
         });
      };

      assertEquals(f(), 10);
   }

   public function testVarGuardedEnum() {
      var s = "apple";

      var res = GSwitch.guarded(switch (EB2("apple")) {
            case EB2(!s): 1;
            default: 0;
      });

      assertEquals(res, 1);
   }

   public function testMultiCase() {
      var res = GSwitch.guarded(switch (EA2(5)) {
            case EA3(y), EA2(y): 1;
            default: 0;
      });

      assertEquals(res, 1);
   } 
 
   public function testMultiCaseGuard() {
      var res = GSwitch.guarded(switch (EA2(5)) {
            case EA3(y), EA2(y) = y > 5: 1;
            default: 0;
      });

      assertEquals(res, 0);
   }


   public function testGuard1() { 
      var res = GSwitch.guarded(switch (EA6(5, 10.0)) {
            case EA3(x): 1;
            case EA6(a, b) = a > 3 && b > 15.0: 2;
            case EA6(a, b) = a > 3 && b == 10.0: 3;
            default: 0;
      });

      assertEquals(res, 3);
   }

   public function testComplex1() {
      var v = 5;

      var res = GSwitch.guarded(switch (EA4(EA4(EA6(5, 10.0)))) {
            case EA4(EA4(x)):
               GSwitch.guarded(switch (x) {
                  case EA6(!v, b) = b < 15.0: 1;
                  default: 0;
               });
            default: 0;
      });

      assertEquals(res, 1);
   }

}
