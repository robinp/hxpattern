import hxpattern.GSwitch;

enum Guard<T> {
   GOk(x: T);
   GFail;
}

class Hxpat { 
 
   @:macro
   public static function gswitch(e: Array<haxe.macro.Expr>) {
      var g = GSwitch._guarded(e);
      #if PRINT_FINAL
      trace(GSwitch.pretty(Std.string(g)));
      #end
      return g;
   }

}
