// antlr4 grammar for dyna



grammar dyna_grammar2;

@header {
package dyna;

import java.math.BigInteger;
//import clojure.java.api.Clojure;
import static dyna.ParserUtils.*;
import clojure.lang.BigInt;

}


// @rulecatch {
//     catch(Exception e) {
//         // just handle any error using a callback into the clojure runtime
//         // the error is either going to be some recognition error or something else
//         // I supppose that this can re-throw the error if it wants
//         Clojure.var("dyna.ast-to-rexpr", "handle-parser-error").invoke(e);
//    }
// }

fragment EndLine
    : [ \t]* ('%' ~[\n\r]*)? [\n\r]
    ;

Comment
    : '%' ~[\n\r]* [\n\r] -> skip
    ;

// the EndTerm symbol has to be followed by a newline or comment otherwise we are uanble to use `.` for both
// ending a statement and dynabases
EndTerm
    : '.' EndLine
    ;

EndQuery
    : '?' EndLine
    ;


Whitespace
    : [ \t\n\r] -> skip
    ;

NormalAtom
    //: ('a'..'z')('a'..'z'|'A'..'Z'|'0'..'9'|'_')*
    : [a-z][a-zA-Z0-9_]* {!("new".equals(getText()))}?
    ;

DollaredAtom
    : '$' [a-z][a-zA-Z0-9_]*
    ;

EscapedAtom
    : '\'' ~['{}() \t\n\r]+ '\''
    ;

Comma
    : ','
    ;

// we can be like a database where there are some values which can be passed by an external method
// these values can just be opaque in the case that we are uanble to figure out their primitive type, otherwise
// this could be used in the case that we don't want to escape something
DollaredExternalValue
    : '$' [0-9]+
    ;


// there is some bug in the antlr4 parser where the first grammar rule after the lexer rules will error
// when using the returns statement
junk1: ;

atom returns[String t]
    : m=NormalAtom { $t = $m.getText(); }
    | m=DollaredAtom { $t = $m.getText(); }
    | m=EscapedAtom
      {
        $t = $m.getText();
        $t = $t.substring(1, $t.length() - 1);
        if($t.startsWith("\$_"))
            throw new DynaSyntaxError("the namespace \$_ is reserved for internal use");
      }
    ;


readAtom returns[String t]
    : a=atom { $t = $a.t; }
    ;

Variable
    : [A-Z_][a-zA-Z0-9_]*
    ;


// going to change this to only match the aggregators which are actually defined
MergedAggregator
    : [&*\-+:|?] '='
    | [a-z][a-z&*\-+:|?_]* '=' {
    // this checks that the aggregator name is defined in rexpr_aggregators.clj and will conditionally enable this lexer rule
        aggregator_defined(getText())}?
    ;

junk2: ;

aggregatorName returns[String t]
// we have to seperate these symbols as they are used in more contexts then just the aggregator
    : '=' { $t = "="; }
    | ':-' { $t = ":-"; }
    | m=MergedAggregator { $t = $m.getText(); }
    ;


// negative is handled in the parser statement otherwise X-1 will fail to parse correctly
NumberInt
    : [0-9]+
    ;

NumberInt16
    : '0x'[0-9a-fA-F]+
    ;

NumberFloat
    : [0-9]* '.' [0-9]+ ('e' '-'? [0-9]+)?  // this always requires some number after the '.' otherwise it could be an end of term
    ;

StringConst
    : '"' (~["\r\n])* '"'
    ;
// ' stupid highlighting

StringConst2
    : '\'' (~['\r\n])* '\''
    ;
// ' stupid highlighting

fragment StringConstBracketsrec
    : '{' ( StringConstBracketsrec | '%' ~[\n\r]* [\n\r] | ~[{}%] )* '}'
    ;

StringConstBrackets
    : '\'' StringConstBracketsrec
    ;

junk3: ;

stringConst returns[String t] locals [String vv]
    : a=StringConst { $vv = $a.getText(); $t = $vv.substring(1, $vv.length() - 1); }
    | a=StringConst2 { $vv = $a.getText(); $t = $vv.substring(1, $vv.length() - 1); }
    | a=StringConstBrackets { $vv = $a.getText(); $t = $vv.substring(2, $vv.length() - 1).replaceAll("%[^\n\r]*([\n\r])", "\$1"); }
    // TODO: we need to handle string escapes etc
    ;

primitive returns[Object v]
    : neg='-'? a=NumberInt {
      BigInteger b = new BigInteger($a.getText());
      if($neg != null) b = b.negate();
      try {
          $v = b.longValueExact();
      } catch (ArithmeticException err) {
          $v = BigInt.fromBigInteger(b);
      }
    }
    | a=NumberInt16 {
      BigInteger b = new BigInteger($a.getText().substring(2), 16);
      try {
          $v = b.longValueExact();
      } catch (ArithmeticException err) {
          $v = BigInt.fromBigInteger(b);
      }
    }
    // question if that should just always use double when inputed, or try and cast down in the case that it can represent
    // or if there should be some special signal such as `0.0f`
    | neg='-'? a=NumberFloat { $v = ($neg != null ? -1 : 1) * java.lang.Double.valueOf($a.getText()); }
    | b=stringConst { $v = $b.t; }
    | 'true' { $v = java.lang.Boolean.valueOf(true); }
    | '$true' { $v = java.lang.Boolean.valueOf(true); }
    | 'false' { $v = java.lang.Boolean.valueOf(false); }
    | '$false' { $v = java.lang.Boolean.valueOf(false); }
    // TODO: should have $null in this list
    ;



// the entry point for parsing a file
program returns[DynaTerm rterm = null]
    : (t=term
       {

          //   // this is not a case that we want to be in.....sigh
          //   System.err.println(_input.getText($term.ctx.getSourceInterval()));
          //   _syntaxErrors++;
          // } else {
          //   // should have already added the term

          // }
          // null out this list such that we do not collect the items over time
          // this lets us parse a MUCH larger file, but it prevents us from having a good error recovery
          // we might want to do something like drop the first 50,000 if the list ever gets above 100,000 or something
          // then we might have some error recovery with some context???
          if(_localctx.children != null && _localctx.children.size() > 2000)
            _localctx.children = null;

              // for the number of different values which this might represent
              // if there is some expression around how this would
        if($t.rterm == null) {
            _syntaxErrors++;
        } else {
            if($rterm == null) {
                $rterm = $t.rterm;
            } else {
                // the term create object should just return true, so we can use ',' to unify it together into a single object
                $rterm = DynaTerm.create(",", $rterm, $t.rterm);
            }
        }
      })* EOF
        // | query EOF
    //   {
    //     // allow for a single entry without any suffix to be treated as a query (so a statement like `a` will be treated like `a?`
    //     //   System.err.println(_input.getText($query.ctx.getSourceInterval()));
    //     //    _syntaxErrors++;
    //     // } else {

    //     // }
    //     // don't bother to null out children as there is only a single item so keeping it will make errors print out nicer
    //   }
        //| termBody {$rterm = $termBody.rterm; }
    ;

// entry point for something that is being evaluated inline, as there might just be some value rather than a defined rule
eval_entry returns [DynaTerm rterm=null]
    : program { $rterm = $program.rterm; }
    | (e=expression Comma {$rterm = $rterm == null ? $e.rterm : DynaTerm.create(",", $rterm, $e.rterm);} )*
       e=expression       {$rterm = $rterm == null ? $e.rterm : DynaTerm.create(",", $rterm, $e.rterm);}
       EOF
    ;

// this version can load the data via a callback rather than constructing a single large object
// in the case that a large file is getting loaded, this would be better as it should avoid having everything in memory all at once
program_LoadAsGo[clojure.lang.IFn callback_function]
    : (t=term {
            callback_function.invoke($t.rterm);
            if(_localctx.children != null && _localctx.children.size() > 2000)
                _localctx.children = null;
        })* EOF
    ;


term returns[DynaTerm rterm = null]
    : term_unended EndTerm {$rterm=$term_unended.rterm;}
    | t=termBody["query="] EndQuery {
            String ttext = $t.ctx.start.getInputStream().getText(new Interval($t.ctx.start.getStartIndex(), $t.ctx.stop.getStopIndex()));
            $rterm = DynaTerm.create("\$query", $t.rterm, ttext, $t.ctx.getStart().getLine());
        }
    | 'assert'
        t=termBody["assert="] EndTerm
        {
            String ttext = $t.ctx.start.getInputStream().getText(new Interval($t.ctx.start.getStartIndex(), $t.ctx.stop.getStopIndex()));
            $rterm = DynaTerm.create("\$assert", $t.rterm, ttext, $t.ctx.getStart().getLine(), true);
        }
    | ('assert_fails'|'assert_fail')
        t=termBody["assert="] EndTerm
        {
            // this is something that should fail with the unification.  So that we can test that something should also return multiplicity 0.
            String ttext = $t.ctx.start.getInputStream().getText(new Interval($t.ctx.start.getStartIndex(), $t.ctx.stop.getStopIndex()));
            $rterm = DynaTerm.create("\$assert", $t.rterm, ttext, $t.ctx.getStart().getLine(), false);
        }

    | 'print'
       t=termBody["print="] EndTerm
       {
            String ttext = $t.ctx.start.getInputStream().getText(new Interval($t.ctx.start.getStartIndex(), $t.ctx.stop.getStopIndex()));
            $rterm = DynaTerm.create("\$print", $t.rterm, ttext, $t.ctx.getStart().getLine());
       }
    | 'debug_repl_clojure'
      t=termBody["print="] EndTerm
      {
           String ttext = $t.ctx.start.getInputStream().getText(new Interval($t.ctx.start.getStartIndex(), $t.ctx.stop.getStopIndex()));
           $rterm = DynaTerm.create("\$_debug_repl", $t.rterm, ttext, $t.ctx.getStart().getLine());
      }
    | 'debug' EndTerm
      { $rterm = DynaTerm.create("\$debug"); }

// there could be warnings if some library is used in a particular way.  This should somehow defer in the case that some dynabase has not been constructed, but this would want to have that the expression would later come into existence
    | 'warning' '(' we=expression ')' t=termBody["warning="] EndTerm
        { // the warning stuff should somehow check something at runtime?
            // Though this is going to need which of the values will correspond with something
            // ideally, this should somehow allow for something to be conditional on some value
            $rterm = DynaTerm.create("\$warning", $we.rterm, $we.ctx.getStart().getLine(), $t.rterm);
            //assert(false);
        }
    ;


// the un-ended term does not consume the EndTerm token at the end.  The EndTerm toekn requires a new line which would require that dynabases have a new line before the closing `}`
term_unended returns[DynaTerm rterm = null]
    locals [DynaTerm dbase_rterm = DynaTerm.null_term]
    : (dbase=expression '.' {$dbase_rterm = $dbase.rterm;})?
      a=atom
      p=parameters
      agg=aggregatorName
      (t=termBody[$agg.t] ';'
            { DynaTerm l = DynaTerm.create("\$define_term", DynaTerm.create_arr($a.t, $p.args), $dbase_rterm, $agg.t, $t.rterm);
              if($rterm == null) $rterm = l;
              else { $rterm = DynaTerm.create(",", $rterm, l); }
             })*
        t=termBody[$agg.t]
        { DynaTerm l = DynaTerm.create("\$define_term", DynaTerm.create_arr($a.t, $p.args), $dbase_rterm, $agg.t, $t.rterm);
              if($rterm == null) $rterm = l;
              else { $rterm = DynaTerm.create(",", $rterm, l);  }
        }
    | (dbase=expression '.'  {$dbase_rterm = $dbase.rterm;})?
        a=atom
      p=parameters
      {
            // writing `a(1,2,3).` is just a short hand for `a(1,2,3) :- true.`
            $rterm = DynaTerm.create("\$define_term", DynaTerm.create_arr($a.t, $p.args), $dbase_rterm, ":-", DynaTerm.create("\$constant", true));
      }
    | ':-' ce=compilerExpression { $rterm = $ce.rterm; }
    ;

// there should be a term which is at the
// term_program returns[DynaTerm rterm = null]



termBody[String aname] returns[DynaTerm rterm]
      locals [
         DynaTerm with_key=null
      ]
    : (e=expression Comma {
            if($rterm == null) {
                $rterm = $e.rterm;
            } else {
                $rterm = DynaTerm.create(",", $rterm, $e.rterm); // the comma operator will return the last value in the expression and unify the first with true
        }
        })* e2=expression {
            if($rterm != null) {
                $rterm = DynaTerm.create(",", $rterm, $e2.rterm);
            } else {
                $rterm = $e2.rterm;
            }
}
      (fe=forExpr {
            // the for expression is something that would be the same as just placing it first in the common expression
                $rterm = DynaTerm.create(",", $fe.rterm, $rterm);
            })?
      (withKey {$with_key = $withKey.rterm;})?
        (fe=forExpr {
                // have the for expression twice as we don't specify if it comes before or after the with_key expression
            // the for expression is something that would be the same as just placing it first in the common expression
                $rterm = DynaTerm.create(",", $fe.rterm, $rterm);
            })?
      {

        if(":-".equals($aname) || "assert=".equals($aname)) {
            // then we want to make the final result be true regardless of what the expression represents
            // this should go before with_key as it is possible that we want some witness to the result
            $rterm = DynaTerm.create(",", $rterm, DynaTerm.create("\$constant", true));
        }
        if($with_key != null) {
            $rterm = DynaTerm.create("\$with_key", $rterm, $with_key);
        }
        if(":=".equals($aname)) {
            $rterm = DynaTerm.create("\$colon_line_tracking",
                                     DynaTerm.create("\$constant", colon_line_counter()),
                                     $rterm);
        }
      }
    ;

withKey returns [DynaTerm rterm]
    : ('arg' | 'with_key') e=expression { $rterm = $e.rterm; }
    ;

forExpr returns [DynaTerm rterm=null]
    : 'for' (e=expression Comma {
        if($rterm == null) { $rterm = $e.rterm; }
        else { $rterm = DynaTerm.create(",", $rterm, $e.rterm); }
    })* e=expression {
        if($rterm == null) { $rterm = $e.rterm; }
        else { $rterm = DynaTerm.create(",", $rterm, $e.rterm); }
    }
    ;

parameters returns [ArrayList<DynaTerm> args]
    :/* empty */ { $args = new ArrayList<>(); }
    //| '(' ')' { $args = new ArrayList<>(); }
    | '(' p=arguments ')' { $args = $p.args; }
    ;

methodName returns [String name]
    : r=readAtom {$name = $r.t;}
    ;

methodCall returns [String name, ArrayList<DynaTerm> args]
    : m=methodName p=parameters
    {
       $name = $m.name;
       $args = $p.args;
    }
    ;

bracketTerm returns [String name, ArrayList<DynaTerm> args]
    : m=methodName '[' p=arguments ']' { $name = $m.name; $args = $p.args; }
    ;


// we could have something like $atoms will just quote their arguments so it
// would be something like a macro a bit, where those somehow expand out more.
// This is the approach that julia takes for its macros.
// there is also the name!() syntax used in rust for macros.  So this would not be without precident.  If there was something dt

// methodCall2[DynaParserInterface prog] returns[String name, ArrayList<Object>
// args] : m=methodName {$m.getText().startswith("$")}? '(' a=arguments[$prog]
// ')' | m=methodName {false}? '(' a=arguments[$prog] ')' ;



arguments returns [ArrayList<DynaTerm> args = new ArrayList<>();]
    : (e=expression Comma {$args.add($e.rterm);})* e=expression {$args.add($e.rterm);} Comma?
    | // zero arguments
    ;

array returns [DynaTerm rterm] locals []
    : '[' elems=arrayElements ']'
        {
            $rterm = DynaTerm.null_term;
            for(int i = $elems.elems.size() - 1; i >= 0; i--) {
                 $rterm = DynaTerm.create("\$cons", $elems.elems.get(i), $rterm);
            }
        }
    | '[' elems=arrayElements '|' t=expression ']'
       {
            $rterm = $t.rterm;
            for(int i = $elems.elems.size() - 1; i >= 0; i--) {
                 $rterm = DynaTerm.create("\$cons", $elems.elems.get(i), $rterm);
            }
       }
    | '[' ']' { $rterm = DynaTerm.null_term; }
    ;

arrayElements returns [ArrayList<DynaTerm> elems = new ArrayList<>(); ]
    : (e=expression Comma {$elems.add($e.rterm);})* e=expression {$elems.add($e.rterm);} Comma?
    ;

assocativeMap returns[DynaTerm rterm]
    : '{' a=assocativeMapInnerBrackets '}' {$rterm=$a.rterm;}
    ;

assocativeMapInnerBrackets returns[DynaTerm rterm]
    : { $rterm = DynaTerm.create("\$map_empty"); }
    | a=assocativeMapElements
        {
            $rterm = DynaTerm.create("\$map_empty");
            for(SimplePair<DynaTerm,DynaTerm> p : $a.elements) {
                $rterm = DynaTerm.create("\$map_element", p.a, p.b, $rterm);
            }
        }
    | a=assocativeMapElements '|' b=expression
        {
            $rterm = $b.rterm;
            for(SimplePair<DynaTerm,DynaTerm> p : $a.elements) {
                $rterm = DynaTerm.create("\$map_element", p.a, p.b, $rterm);
            }
        }
    ;

assocativeMapElements returns[ArrayList<SimplePair<DynaTerm,DynaTerm>> elements = new ArrayList<>();]
    : (a=assocativeMapElement Comma  {$elements.add(new SimplePair($a.key, $a.value));} )*
       a=assocativeMapElement Comma? {$elements.add(new SimplePair($a.key, $a.value));}
    ;

assocativeMapElement returns[DynaTerm key, DynaTerm value]
    : v=Variable { $key = DynaTerm.create("\$constant", $v.getText()); $value = DynaTerm.create("\$variable", $v.getText()); }
    | a=expression '->' b=expression {$key=$a.rterm; $value=$b.rterm;}
    ;


dynabase returns[DynaTerm rterm]
    locals [DynaTerm dterms=DynaTerm.null_term]
    : 'new' '(' parent=expression ')' {$rterm=DynaTerm.create("\$dynabase_create", $parent.rterm, DynaTerm.null_term);}
    | 'new' parent=expression '{' (dd=dynabaseInnerBracketTerms {$dterms=$dd.dterms;})? '}' {$rterm=DynaTerm.create("\$dynabase_create", $parent.rterm, $dterms);}
    | 'new' '{' (dd=dynabaseInnerBracketTerms {$dterms=$dd.dterms;})? '}' {$rterm=DynaTerm.create("\$dynabase_create", DynaTerm.null_term, $dterms);}
    | '{' d=dynabaseInnerBracket '}'  {$rterm=$d.rterm;}
    ;


dynabaseInnerBracket returns[DynaTerm rterm]
    : dd=dynabaseInnerBracketTerms {$rterm=DynaTerm.create("\$dynabase_create", DynaTerm.null_term, $dd.dterms);}
    ;

dynabaseInnerBracketTerms returns[DynaTerm dterms=null]
    : (t=term_unended EndTerm {$dterms = ($dterms == null ? $t.rterm : DynaTerm.create(",", $dterms, $t.rterm));})*
       t=term_unended (EndTerm|'.') {$dterms = ($dterms == null ? $t.rterm : DynaTerm.create(",", $dterms, $t.rterm));} // the new line after the last term in a dynabase is optional
    ;


// possible that the `(X) = foo` will get confused with unification.  In which case this will need something else for the syntax of an equals aggregator?
inlineFunction2 returns [DynaTerm rterm]
locals [ArrayList<DynaTerm> argslist = null, ArrayList<DynaTerm> bodies = new ArrayList()]
    : '(' ('(' {$argslist = new ArrayList<>();}
              ((v=Variable Comma {$argslist.add(DynaTerm.create("\$variable", $v.getText()));})*
                v=Variable Comma? {$argslist.add(DynaTerm.create("\$variable", $v.getText()));})? ')' )?
          agg=aggregatorName
         (t=termBody[$agg.t] ';' {$bodies.add($t.rterm);})*
          t=termBody[$agg.t] {$bodies.add($t.rterm);} ')'
      { $rterm = DynaTerm.create("\$inline_function", $argslist == null ? DynaTerm.null_term : DynaTerm.create_arr("x", $argslist),
                                                     $agg.t, DynaTerm.make_list($bodies)); }
    ;




// this is apparently the suggested way to deal with order of operators in antlr
expressionRoot returns [DynaTerm rterm]
    : m=methodCall { $rterm = DynaTerm.create_arr($m.name, $m.args); }
    | '&' m=methodCall {
          $rterm = DynaTerm.create("\$quote1", DynaTerm.create_arr($m.name, $m.args)); }
    // | '&' dbase=expression '.' m=methodCall {
    //         assert(false);
    //        $rterm = DynaTerm.create("\$dynabase_quote1", $dbase.rterm, DynaTerm.create_arr($m.name, $m.args));
    //     }
    | brt=bracketTerm { $rterm = DynaTerm.create("\$quote1", DynaTerm.create_arr($brt.name, $brt.args)); }
    | v=Variable {
            if($v.getText().equals("_")) {
                // this is an anon variable that is not referenced from multiple places
                $rterm = DynaTerm.create("\$variable", gensym_variable_name());
            } else {
                $rterm = DynaTerm.create("\$variable", $v.getText());
            }
      }
    | primitive { $rterm = DynaTerm.create("\$constant", $primitive.v); }
    | '(' e=expression ')' { $rterm = $e.rterm; }
    | ilf=inlineFunction2 { $rterm = $ilf.rterm; }
    | a=array { $rterm = $a.rterm; }
    | ':' m=methodCall {  // for supporting things like f(:int) => f(_:int)
            $rterm = DynaTerm.create("\$variable", gensym_variable_name());
            $m.args.add($rterm);
            $rterm = DynaTerm.create(",", DynaTerm.create($m.name, $m.args), $rterm); }
    | mp=assocativeMap { $rterm=$mp.rterm; }
    | db=dynabase { $rterm = $db.rterm; }
    | v=Variable '(' arguments ')' {
            if($v.getText().equals("_")) {
                throw new DynaSyntaxError("Calling an unscore function is not supported");
            }
            // for doing an indirect call to some value
            $arguments.args.add(0, DynaTerm.create("\$variable", $v.getText()));
            $rterm = DynaTerm.create_arr("\$call", $arguments.args);
        }
    | '(' e=expression ')' '(' arguments ')' {
        $arguments.args.add(0, $e.rterm);
        $rterm = DynaTerm.create_arr("\$call", $arguments.args);
       }
    | '`' '(' e=expression ')' { $rterm = DynaTerm.create("\$escaped", $e.rterm); }
    | '`' v=Variable { $rterm = DynaTerm.create("\$escaped", DynaTerm.create("\$variable", $v.getText())); }
    | '*' { $rterm = DynaTerm.create("\$self_term_uid"); }
    | dd=DollaredExternalValue { $rterm = DynaTerm.create("\$external_value", Long.parseLong($dd.getText().substring(1))); }
    ;



expressionDynabaseAccess returns[DynaTerm rterm]
    : a=expressionRoot {$rterm=$a.rterm;}
      ('.' m=methodCall {
                if($rterm.name.equals("\$quote") || $rterm.name.equals("\$inline_function")) {
                    throw new DynaSyntaxError();//"syntax error");
                    //assert(false); /// should be a syntax error
                }
                if($rterm.name.equals("\$quote1")) {
                    // this is something like `&f(5).foo` which should be converted into `f(5).foo[]`
                    $rterm = DynaTerm.create("\$dynabase_quote1", $rterm.get(0), DynaTerm.create_arr($m.name, $m.args));
                } else if($rterm.name.equals("\$dynabase_quote1")) {
                    $rterm = DynaTerm.create("\$dynabase_quote1", DynaTerm.create("\$dynabase_call", $rterm.get(0), $rterm.get(1)),
                                                                  DynaTerm.create_arr($m.name, $m.args));
                } else {
                    $rterm = DynaTerm.create("\$dynabase_call", $rterm, DynaTerm.create_arr($m.name, $m.args));
                }
        })*
      ('.' bracketTerm {
        if($rterm.name.equals("\$quote") || $rterm.name.equals("\$quote1") || $rterm.name.equals("\$dynabase_quote1")) {
            throw new DynaSyntaxError("Structured terms can not be used as a dynabase");
        }
        $rterm = DynaTerm.create("\$dynbase_quote1", $rterm, DynaTerm.create_arr($bracketTerm.name, $bracketTerm.args)); })?
    ;

expressionAddBrakcetsCall returns [DynaTerm rterm]
locals [DynaTerm add_arg=null]
    : a=expressionDynabaseAccess  { $rterm = $a.rterm; }
    | a=expressionDynabaseAccess ('{'
            // this could get the current symbol at a given location, and then capture the string between two symbols
            // that could allow for this expression to do "whatever it wants" between a block of {} stuff
            (db=dynabaseInnerBracket {$add_arg=$db.rterm;}
            | nm=assocativeMapInnerBrackets {$add_arg=$nm.rterm;})
            '}'
        |   str=StringConstBrackets {
                    String lstr = $str.getText();
                    $add_arg = DynaTerm.create("\$constant", lstr.substring(2, lstr.length() - 1).replaceAll("%[^\n\r]*([\n\r])", "\$1"));
                    }
        )
        {
            $rterm = $a.rterm;
            assert($add_arg != null);
            if($rterm.name.equals("\$quote1") || $rterm.name.equals("\$quote") || $rterm.name.equals("\$constant")
               || $rterm.name.equals("\$escaped") || $rterm.name.equals("\$inline_function") || $rterm.name.equals("\$dynabase_quote1")
               || $rterm.name.equals("\$dynabase_create") || $rterm.name.equals("\$map_empty") || $rterm.name.equals("\$map_element")
               || $rterm.name.equals("\$nil") || $rterm.name.equals("\$cons"))
               {
               throw new DynaSyntaxError("Implicit call using {} can only be done to a term");
               }
            if($rterm.name.equals("\$dynabase_call")) {
                // have to put the argument onto the dynabase call element,
                $rterm = DynaTerm.create($rterm.name, $rterm.get(0), ((DynaTerm)$rterm.get(1)).extend_args($add_arg));
            } else if($rterm.name.equals("\$variable")) {
                $rterm = DynaTerm.create("\$call", $rterm, $add_arg); // to support expressions like `X { x=123. }` which are like `X(){ x=123.}`
            } else {
                $rterm = $rterm.extend_args($add_arg);
            }
        }
    ;

expressionTypedUnioned returns [DynaTerm rterm]
    : b=methodCall {$rterm = DynaTerm.create_arr($b.name, $b.args);}
        ('|' b=methodCall {
                $rterm = DynaTerm.create("\$union_type",
                                         DynaTerm.create("\$quote1", $rterm),
                                         DynaTerm.create("\$quote1", DynaTerm.create_arr($b.name, $b.args)));
            })*
    ;

expressionTyped returns [DynaTerm rterm]
locals [DynaTerm result_variable]
    : a=expressionAddBrakcetsCall {$rterm=$a.rterm;}
    | a=expressionAddBrakcetsCall {
            $result_variable = DynaTerm.create("\$variable", gensym_variable_name());
            $rterm = DynaTerm.create("\$unify", $result_variable, $a.rterm);
        }
        (':' b=expressionTypedUnioned {
                $rterm = DynaTerm.create(",", $rterm, $b.rterm.extend_args($result_variable));
            })+
        {$rterm = DynaTerm.create(",", $rterm, $result_variable);}
    ;


expressionUnaryMinus returns [DynaTerm rterm]
    : b=expressionTyped {$rterm = $b.rterm;}
    | '-' b=expressionTyped {$rterm = DynaTerm.create("\$unary_-", $b.rterm);}
    ;

expressionExponent returns [DynaTerm rterm]
    : b=expressionUnaryMinus {$rterm = $b.rterm;}
    | a=expressionUnaryMinus '**' b=expressionUnaryMinus {$rterm = DynaTerm.create("**", $a.rterm, $b.rterm);}
    ;

expressionMultiplicative returns [DynaTerm rterm]
    : a=expressionExponent {$rterm = $a.rterm;} (op=('*'|'/') b=expressionExponent  // removed // for the int division. not sure if that is needed given we have a builtin range expression which only works for int expressions
                {$rterm = DynaTerm.create($op.getText(), $rterm, $b.rterm);})*
    ;

expressionAdditive returns [DynaTerm rterm]
    : a=expressionMultiplicative {$rterm = $a.rterm;} (op=('+'|'-') b=expressionMultiplicative
            {$rterm = DynaTerm.create($op.getText(), $rterm, $b.rterm);})*
    ;

expressionNot returns [DynaTerm rterm]
    : a=expressionAdditive {$rterm=$a.rterm;}
    | '!' a=expressionAdditive {$rterm = DynaTerm.create("!", $a.rterm);}
    ;

expressionRelationCompare returns [DynaTerm rterm]
locals[ArrayList<DynaTerm> expressions, ArrayList<String> ops]
    : a=expressionNot {$rterm = $a.rterm;}
    | a=expressionNot {
          $expressions = new ArrayList<>();
          $ops = new ArrayList<>();
          $expressions.add($a.rterm);
      }
      (op=('>'|'<'|'<='|'>=') b=expressionNot
          { $ops.add($op.getText());
            $expressions.add($b.rterm);
          })+
      {
          // this creates tmp vars for all of the values used more than once, but they are now evaluated out of order?
          // given the declaritive nature of the program, that shouldn't be a "problem" per say
          $rterm = null;
          for(int i = 1; i < $expressions.size() - 1; i++) {
              // this isn't needed in the case that the nested expression is a variable or constant
              // those can just get duplicated
              if(!("\$variable".equals($expressions.get(i).name) || "\$constant".equals($expressions.get(i).name))) {
                  DynaTerm tmp_var = DynaTerm.create("\$variable", gensym_variable_name());
                  DynaTerm uf = DynaTerm.create("\$unify", tmp_var, $expressions.get(i));
                  $rterm = $rterm == null ? uf : DynaTerm.create(",", $rterm, uf);
                  $expressions.set(i, tmp_var);
              }
          }
          for(int i = 0; i < $ops.size(); i++) {
              DynaTerm o = DynaTerm.create($ops.get(i), $expressions.get(i), $expressions.get(i+1));
              $rterm = $rterm == null ? o : DynaTerm.create(",", $rterm, o);
          }
      }
      ;

expressionEqualsCompare returns [DynaTerm rterm]
    : a=expressionRelationCompare {$rterm = $a.rterm;}
        (op=('=='|'!=') b=expressionRelationCompare
            {$rterm = DynaTerm.create($op.getText(), $rterm, $b.rterm);})*
    ;

expressionLogical returns [DynaTerm rterm]
    : a=expressionEqualsCompare {$rterm = $a.rterm;}
        (op=('||'|'&&') b=expressionEqualsCompare
            {$rterm = DynaTerm.create($op.getText(), $rterm, $b.rterm);})*
    ;

expressionIs returns [DynaTerm rterm]
    : a=expressionLogical {$rterm=$a.rterm;}
    | a=expressionLogical ('is'|'=') b=expressionLogical
        {$rterm = DynaTerm.create("\$unify", $a.rterm, $b.rterm);}
    ;

expression returns [DynaTerm rterm]
    : a=expressionIs { $rterm = $a.rterm; }
    ;

compilerExpressionArgument returns [Object val]
    locals [ArrayList<Object> args=null]
    : p=primitive {$val=$p.v;}
    | {$args=new ArrayList<>();} a=atom ('(' ((ag=compilerExpressionArgument Comma {$args.add($ag.val);})*
                                              ag=compilerExpressionArgument Comma? {$args.add($ag.val);})?  ')' )?
      {$val = DynaTerm.create_arr($a.t, $args); }
    | '*' {$val = "*";}
    | '**' {$val = "**";}
    | '&' {$val = "&";}
    | '&&' {$val = "&&";}
    | '+' {$val = "+";}
    | '-' {$val = "-";}
    ;

compilerExpressionParams returns [ArrayList<Object> args = new ArrayList<>()]
    : /* empty */ {}
    | '(' ')'
    | '(' (p=compilerExpressionArgument { $args.add($p.val); } Comma)*
           p=compilerExpressionArgument { $args.add($p.val); } Comma? ')'
    | pr=primitive {$args.add($pr.v);}
    ;

// should maybe make the list of the compiler intrinsics explicit in the parser, this is fairly general atm
compilerExpression returns [DynaTerm rterm]
locals [ArrayList<Object> args]
    : 'import'  {$args = new ArrayList<>();}
        (m=methodId Comma  {$args.add($m.rterm);})*
         m=methodId Comma? {$args.add($m.rterm);}
      'from' name=stringConst {
         $rterm = DynaTerm.create("\$compiler_expression", DynaTerm.create("import", DynaTerm.make_list($args), $name.t));
      }
    | 'from' name=stringConst
      'import' {$args = new ArrayList<>();}
        (m=methodId Comma  {$args.add($m.rterm);})*
         m=methodId Comma? {$args.add($m.rterm);}
      {
         $rterm = DynaTerm.create("\$compiler_expression", DynaTerm.create("import", DynaTerm.make_list($args), $name.t));
      }
    | 'import' name=stringConst {
         $rterm = DynaTerm.create("\$compiler_expression", DynaTerm.create("import", $name.t));
       }
    // TODO: there is some redudancy in the way that expressions could be
    // encoded by this.  But the encodings are going to generate _different_
    // ASTs
    | a=atom p=compilerExpressionParams {$rterm = DynaTerm.create("\$compiler_expression", DynaTerm.create_arr($a.t, $p.args));}
    | a=atom b=atom p=compilerExpressionParams {$rterm = DynaTerm.create("\$compiler_expression", DynaTerm.create($a.t, DynaTerm.create_arr($b.t, $p.args)));}
    | a=atom m=methodId { $rterm = DynaTerm.create("\$compiler_expression", DynaTerm.create($a.t, $m.rterm)); }
    | e=expression {$rterm=DynaTerm.create("\$compiler_expression", $e.rterm);}
;

methodId returns [DynaTerm rterm]
    : a=atom '/' b=NumberInt { $rterm = DynaTerm.create("/", $a.t, java.lang.Long.valueOf($b.getText())); }
    | a=atom { $rterm = DynaTerm.create("/", $a.t, 0L); }
    ;
