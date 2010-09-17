#if macro

import haxe.macro.Expr;
import haxe.macro.Context;

typedef GuardConstExpr = {
   gvar: Null<Expr>,
   econst: Array<Expr>
}

#end // macro

enum Guard<T> {
   GOk(x: T);
   GFail;
}

class GSwitch
{
#if macro
	public static function mk(e,?pos) : Expr {
		return {expr:e, pos:pos==null?Context.currentPos():pos};
   }
	
   static function mkGOk(e: Expr): Expr {
      return mk(ECall(
               mk(EConst(CType("GOk"))), 
               [ e ]
             ));
   }

   static function mkGFail(): Expr {
      return mk(EConst(CType("GFail")));
   }

   static function mkGuardVar(
         varidx: Int, 
         orig_expr: Expr, 
         elist: List<GuardConstExpr>, 
         new_args: Array<Expr>): Int {


      var v = mk(EConst(CIdent("__gv" + varidx++)));

      new_args.push(v);
      elist.add({
         econst: [orig_expr], 
         gvar: v
      });

      return varidx;
   }

   static function caseExpand(elist: List<GuardConstExpr>, varidx: Int, guard: Expr, block: Expr): Expr {
      return if (elist.isEmpty()) {
         var core = mk(EBlock([
            mk(EVars([
               { name: "__blk", type: null, expr: block }
            ])),
            mkGOk( mk(EConst(CIdent("__blk"))) )
         ]));

         if (guard == null) {
            core;
         }
         else {
            mk(EIf(
               guard, 
               core,
               mkGFail()
            ));
         }
      }
      else {
         var h = elist.pop();

         var case_val_expr = {
               
            // preprocessing for guard
               var case_len = h.econst.length;

               switch (h.econst[case_len - 1].expr) {
                  default: // pass
                  case EBinop(op, e1, e2):
                     switch (op) {
                        default: // pass
                        case OpAssign:
                           // replace expr with left-hand,
                           // add guard with right-hand
                           h.econst[case_len - 1] = e1;
                           guard = e2;
                     }
               }
            
               // value of case_val_expr
               switch (h.econst[0].expr) {

                  default:
                     // not supported expressions are left as-is
                     h.econst;

                  case ECall(called, args):
                     switch (called.expr) {
                        default:
                           h.econst; // possibly method call
                        case EConst(c):
                           switch (c) {
                              default: 
                                 h.econst; // funcall
                              case CType(enum_type):

                                 // enum
                                 
                                 // extract non-vars (
                                 //    - e.EConst(anything except CIdent)
                                 //    - e.ECall  (enum or funcall)
                                 //    - e.EUnop(OpNot(), false, e.EConst(CIdent(x))), which is !x
                                 //      marking that x is not to be bound but to be matched on as
                                 //      an existing var 
                                 // from the enum arguments and replace with generated
                                 // variables (while also recording the variables
                                 // and the corresponding expressions)
                                 
                                 var new_args = []; // will contain the existing or generated variables

                                 for (arg_expr in args) {

                                    // proof-check multi-case: only identifiers allowed
                                    //
                                    // we only check the first case-val, others will be dealt with
                                    // by Haxe after the macro substitution
                                    if (case_len > 1) switch (arg_expr.expr) {
                                       default: throw "multi-val case: only identifiers allowed";
                                       case EConst(c):
                                          switch (c) {
                                             default: throw "multi-val case: only identifiers allowed";
                                             case CIdent(_): // pass, ok
                                          }
                                    }

                                    // transform args
                                    switch (arg_expr.expr) {
                                       case EConst(c):
                                          switch (c) {
                                             case CIdent(_):
                                                // don't transform
                                                new_args.push(arg_expr);

                                             default:
                                                varidx = mkGuardVar(varidx, arg_expr, elist, new_args);

                                          } // switch (c)

                                       case ECall(_, _):
                                          varidx = mkGuardVar(varidx, arg_expr, elist, new_args);

                                       case EUnop(op, _, e):
                                          switch (op) {
                                             case OpNot:
                                                varidx = mkGuardVar(varidx, e, elist, new_args);
                                             
                                             default:
                                                throw ("Only ! operator supported in enum-match: " +arg_expr);

                                          } // switch (op)

                                       default:
                                          throw ("Not supported expr in enum arg-match: " + arg_expr);
                                    } // switch (arg_expr.expr)
                                 } // for (arg_expr in args)

                                 var res = [ 
                                    mk(ECall(
                                       called, 
                                       new_args
                                    )) 
                                 ];

                                 if (case_len > 1) {
                                    for (i in 1...case_len) {
                                       res.push(h.econst[i]);
                                    }
                                 }

                                 // ret val
                                 res;

                           } // switch (c)

                        // case EConst(c)

                     } // switch (called.expr)

                  // case ECall(called, args)
               
               } // switch (h.econst[0].expr)

            } // case_val_expr = if (...)

         // retval
         mk(ESwitch(
            h.gvar,
            [{
               values: case_val_expr,
               expr: caseExpand(elist, varidx, guard, block)
            }],
            mkGFail()
         ));

      }
   }


   public static function pretty(s: String) {
      var ind = 0;

      var mkIndent = function (i) {
         var s = "";
         for (k in 0...i)
            s += "   ";
         return s;
      };

      var o = new haxe.io.BytesOutput();
      for (i in 0...s.length) {
         var c = s.charAt(i);
         switch (c) {
            case '{', '[':
               o.writeString("\n" + mkIndent(ind) + c);
               ind++;
            case '}', ']':
               ind--;
               o.writeString("\n" + mkIndent(ind) + c);
            case '\n':
               o.writeString(mkIndent(ind));
            default:
               o.writeString(c);
         }
      }
      return o.getBytes().toString();
   }

   static function genSwitch(
         on : Expr,
         cases: Array<{values: Array<Expr>, expr: Expr}>,
         def: Null<Expr>
   ) : Expr
   {
      return if (cases.length == 0) {
         // generate default branch
         def;
      }
      else {
         var cse = cases.shift();

         var expr_q = new List<GuardConstExpr>();
         expr_q.add({
            gvar: on, 
            econst: cse.values
         });

         mk(ESwitch(
            caseExpand(expr_q, 0, null /* guard */, cse.expr),
            [{
               values: [ mkGOk(mk(EConst(CIdent("__gres")))) ],
               expr: mk(EConst(CIdent("__gres")))
            }],
            genSwitch(on, cases, def) // recurse if no match
         ));
      }
   }

   public static function _guarded(e: Expr) {

      return switch (e.expr) {
         case ESwitch(on, cases, def):
            if (def == null) {
               throw "Default must be provided for guarded-switch";
            }

            // put "on" into a separate var to 
            // avoid multi-call or evalutaion
            mk(EBlock([
               mk(EVars([
                  { name: "__gupon", type: null, expr: on }
               ])),
               genSwitch(
                  mk(EConst(CIdent("__gupon"))), 
                  cases, 
                  def)
            ]));

         default:
            throw "Switch expected for " + e;
      }
   }
#end // macro

   @:macro
   public static function guarded(e: Expr) {
      var g = _guarded(e);
      #if PRINT_FINAL
      trace(pretty(Std.string(g)));
      #end
      return g;
   }

}


