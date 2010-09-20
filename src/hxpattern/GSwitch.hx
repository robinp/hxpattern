package hxpattern;

#if macro

import haxe.macro.Expr;
import haxe.macro.Context;

typedef GuardConstExpr = {
   gvar: Null<Expr>,
   econst: Array<Expr>
}

typedef GSwitchData = {
   on: Expr,
   def: Expr,
   cases: Array<{
      values: Array<Expr>,
      expr: Expr,
      guard: Null<Expr>
   }>
}

#end // macro

enum Guard<T> {
   GOk(x: T);
   GFail;
}

class GSwitch
{
#if macro

   // ----- generally useful expression manipulation -----

	public static function mk(e,?pos) : Expr {
		return {expr:e, pos:pos==null?Context.currentPos():pos};
   }

   public static function mkIdent(refname: String) {
      return mk(EConst(CIdent(refname)));
   }

   public static function mkCType(tname: String) {
      return mk(EConst(CType(tname)));
   }

   public static function mkStaticField(cls: String, field: String) {
      return mk(EField(mk(EConst(CType(cls))), field));
   }

   public static function mkStaticCall(cls: String, field: String, args: Array<Expr>) {
      return mk(ECall(
         mkStaticField(cls, field),
         args
      ));
   }
	
   // ----- GSwitch specific expression manipulation -----

   static function mkGOk(e: Expr): Expr {
      return mk(ECall(
               mk(EConst(CType("GOk"))), 
               [ e ]
             ));
   }

   static function mkGFail(): Expr {
      return mk(EConst(CType("GFail")));
   }

   static function mkInnerSwitch(on: Expr, val_expr_array) {
      return mk(ESwitch(
         on, val_expr_array, mkGFail()
      ));
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

   static function rewriteTypeAndGetName(
            t: Expr, 
            field: String, 
            args: Null<Array<Expr>>,
            arr: Array<Expr>, 
            i: Int) 
   { 
      // capture enums in the format EnumName.EN1(...)
      // for the purpose of runtime type checking
      //
      // once haxe.macro gets type query
      // support API, this could be more elegant

      return switch (t.expr) {
         default: throw "unxpected: " + t;

         case EType(_, _):
            throw "please import the package containing the enum for GSwitch";

         case EConst(c):
            switch (c) {
               default: throw "unxpected: " + t;
               case CType(s):
                  arr[i] = if (args == null) {
                     mkCType(field);
                  }
                  else {
                     mk(ECall(
                        mkCType(field),
                        args ));
                  };

                  // retval
                  s;
            }
      };
   }

   static function caseExpand(?top = true, elist: List<GuardConstExpr>, varidx: Int, guard: Expr, block: Expr): Expr {
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

         var case_types: Null<String> = null;

         var case_val_expr = {
               
               var case_len = h.econst.length;

               // check for transforming constructors with enum types 

               var update_check_case_types = function(s: String) {
                  if (case_types == null) {
                     case_types = s;
                  }
                  else if (case_types != s) {
                     throw "All case-values in a multi-case should have same EnumType";
                  }
               };

               for (i in 0...case_len) {
                  switch (h.econst[i].expr) {
                     default: //pass

                     case EType(t, f):

                        update_check_case_types(
                              rewriteTypeAndGetName(t, f, null, h.econst, i) );

                     case ECall(called, args):
                        switch (called.expr) {
                           default: //pass
                           case EType(t, f):
                              
                              update_check_case_types(
                                    rewriteTypeAndGetName(t, f, args, h.econst, i) );
                              
                        } // switch (called)
                  } // switch (h.econst[i].expr)
               } // for (i)

               // value of case_val_expr
               switch (h.econst[0].expr) {

                  default:
                     // not supported expressions are left as-is
                     h.econst;

                  case ECall(called, args):
                     switch (called.expr) {
                        default:
                           h.econst; // possibly method call via EField ?


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

         var val_expr_arr = [{
            values: case_val_expr,
            expr: caseExpand(false, elist, varidx, guard, block)
         }];


         // retval
         if (case_types == null) {
            mkInnerSwitch(h.gvar, val_expr_arr);
         }
         else {
            // wrap into type-check and cast
            mk(EIf(
               // condition
               mkStaticCall("Std", "is", [h.gvar, mkCType(case_types)]),
               // if-branch
               mk(EBlock([
                  mk(EVars([{
                     name: "__g_cast", 
                     type: null,
                     expr: mk(ECast(
                        h.gvar,
                        TPath({
                           pack: [],
                           name: case_types,
                           params: [],
                           sub: null
                        })
                     ))
                  }])),
                  // value of block
                  mkInnerSwitch(
                     mkIdent("__g_cast"),
                     val_expr_arr
                  )
               ])),
               // else-branch
               mkGFail() 
            ));
         }


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
         cases: Array<{values: Array<Expr>, expr: Expr, guard: Null<Expr>}>,
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
            caseExpand(expr_q, 0, cse.guard, cse.expr),
            [{
               values: [ mkGOk(mk(EConst(CIdent("__gres")))) ],
               expr: mk(EConst(CIdent("__gres")))
            }],
            genSwitch(on, cases, def) // recurse if no match
         ));
      }
   }

   static var GSWITCH_USAGE = 
      "GSwitch takes arguments <on>, [<case1_1 [& case1_2 & ...] [ | (<guard expr>)] = <expr> >, ...], _ = <default>\n\t(<on> must be the first argument, _ = <default> can be second or last";

   static function arrayFromAndOp(e: Expr, cases: Array<Expr>) {
      return switch (e.expr) {
         default:
            cases.push(e);
            cases.reverse();
            cases;

         case EBinop(op, e1, e2):
            switch(op) {
               default:
                  cases.push(e);
                  cases.reverse();
                  cases;

               case OpAnd:
                  cases.push(e2);
                  arrayFromAndOp(e1, cases);
            }
      };
   }

   static function checkAndGetDefault(e: Expr): Null<Expr> {
      return switch (e.expr) {
         default: null;
         case EBinop(op, e1, e2):
            switch (op) {
               default: null;
               case OpAssign:
                  switch (e1.expr) {
                     default: null;
                     case EConst(c):
                        switch (c) {
                           default: null;
                           case CIdent(s):
                              if (s == "_")
                                 e2;
                              else
                                 null;                              
                       }
                 }
           } 
      };
   }

   static function extractGSwitchData(e: Array<Expr>): GSwitchData {
      // validate input arguments

      if (e.length < 2)
         throw GSWITCH_USAGE;

      // first parameter (=switch-var) can't contain assignment
      switch (e[0].expr) {
         default: //pass
         case EBinop(op, _, _):
            switch (op) {
               default: //pass
               case OpAssign:
                  throw GSWITCH_USAGE;
            }
      }

      var def: Expr = null;
      var a_begin = 1;
      var a_end = e.length;
      
      def = checkAndGetDefault(e[1]);

      if (def != null) {
         a_begin++;
      }
      else {
         if (e.length <= 2)
            throw GSWITCH_USAGE;
         
         def = checkAndGetDefault(e[e.length - 1]);

         if (def != null) {
            a_end--;
         }
         else
            throw GSWITCH_USAGE;
      }


      var data = {
         on: e[0],
         def: def,
         cases: []
      };

      // now extract info from the cases

      for (i in a_begin...a_end) {
         switch (e[i].expr) {
            default:
               throw GSWITCH_USAGE + "\nfor: " + Std.string(e[i]);
            case EBinop(op, e1, e2):
               switch (op) {
                  default: 
                     throw GSWITCH_USAGE + "\nfor: " + Std.string(e[i]);
                  case OpAssign:
                     var block = e2;
                     var guard: Expr = null;

                     var values = switch (e1.expr) {
                        case EBinop(op, eo1, eo2):
                           switch (op) {
                              case OpOr:
                                 guard = eo2;
                                 arrayFromAndOp(eo1, []);
                              case OpAnd:
                                 arrayFromAndOp(e1, []);
                              default: 
                                 [ e1 ];
                           }
                        default:
                           [ e1 ];
                     }

                     data.cases.push({
                        values: values,
                        expr: block,
                        guard: guard
                     });
               }
         }
      } // end for

      return data;
   }

   public static function _guarded(e: Array<Expr>) {

      var gdata = extractGSwitchData(e);

      // put "on" into a separate var to 
      // avoid multi-call or evalutaion
      return mk(EBlock([
         mk(EVars([
            { name: "__gupon", type: null, expr: gdata.on }
         ])),
         genSwitch(
            mk(EConst(CIdent("__gupon"))), 
            gdata.cases, 
            gdata.def)
      ]));
   }
#end // macro


}


