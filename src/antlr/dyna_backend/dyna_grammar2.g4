// antlr4 grammar for dyna



// some bug that prevents us from having this loaded in a package
// looks like it might be how the build script is trying to locate items
// also unable to use any additional tools from antlr when using a package name...lame
grammar dyna_grammar2;
//
@header {
package dyna_backend;//.genparser;

//import dyna_backend.DynaParserInterface2;
}

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
    : [a-z][a-zA-Z0-9_]*
    ;

DollaredAtom
    : '$' [a-z][a-zA-Z0-9_]*
    ;

EscapedAtom
    : '\'' ~[']+ '\''
    ;
// '

Comma
    : ','
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
            throw new RuntimeException("the namespace \$_ is reserved for internal use");
      }
    ;


// for the fact that you aren't allowed to set to the $variable things
readAtom returns[String t]
//    : n=DollaredAtom { $t = $n.getText();  }
    : a=atom { $t = $a.t; }
    ;

Variable
    : [A-Z_][a-zA-Z0-9_]*
    ;

MergedAggregator
    : [!@#$^&*\-+:|] '='
    | [a-z][a-z!@#$^&*\-+:|]* '='
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
    : [0-9]* '.' [0-9]+ ('e' [0-9]+)?
    ;

StringConst
    : '"' (~["\r\n])* '"'
    ;
// ' stupid highlighting

StringConst2
    : '\'' (~['\r\n])* '\''
    ;
// ' stupid highlighting

junk3: ;

// if we want to support multilined strings in the future or something, we can just do that here
stringConst returns[String t] locals [String vv]
    : a=StringConst { $vv = $a.getText(); $t = $vv.substring(1, $vv.length() - 1); }
    | a=StringConst2 { $vv = $a.getText(); $t = $vv.substring(1, $vv.length() - 1); }
    // TODO: we need to handle string escapes etc
    ;

primitive returns[Object v]
    // TODO: automatically choose the correct representation size for these objects depending on what value they are
    : neg='-'? a=NumberInt { $v = ($neg != null ? -1 : 1) * java.lang.Integer.valueOf($a.getText()); }
    | a=NumberInt16 { $v = java.lang.Integer.valueOf($a.getText().substring(2), 16); }
    // TODO: have support for bigger 64 bit doubles
    // question if that should just always use double when inputed, or try and cast down in the case that it can represent
    // or if there should be some special signal such as `0.0f`
    | neg='-'? a=NumberFloat { $v = ($neg != null ? -1 : 1) * java.lang.Float.valueOf($a.getText()); }
    | b=stringConst { $v = $b.t; }
    | 'true' { $v = java.lang.Boolean.valueOf(true); } // these possibly get confused as aggregators if used like true=
    | '$true' { $v = java.lang.Boolean.valueOf(true); }
    | 'false' { $v = java.lang.Boolean.valueOf(false); }
    | '$false' { $v = java.lang.Boolean.valueOf(false); }
    // TODO: should have $null in this list
    ;


program returns[Object rterm]
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
         if($rterm == null) {
             $rterm = $t.rterm;
         } else {
             // the term create object should just return true, so we can use ',' to unify it together into a single object
             $rterm = DynaTerm.create(",", $rterm, $t.rterm);
         }
      })* EOF
    | query EOF
      {
        // allow for a single entry without any suffix to be treated as a query (so a statement like `a` will be treated like `a?`
        //   System.err.println(_input.getText($query.ctx.getSourceInterval()));
        //    _syntaxErrors++;
        // } else {

        // }
        // don't bother to null out children as there is only a single item so keeping it will make errors print out nicer
      }
    ;


term returns[Object rterm = null]
    locals [Object dbase_rterm = null]
    :
        (dbase=expression '.' {$dbase_rterm = $dbase.rterm;  assert(false);})?
      a=atom
      p=parameters
      agg=aggregatorName
      (t=termBody ';'
            { Object l = DynaTerm.create("\$define_term", DynaTerm.create_arr($a.t, $p.args), $agg.t, $t.rterm);
              if($rterm == null) $rterm = l;
              else { $rterm = DynaTerm.create(",", $rterm, l); }
             })*
        t=termBody EndTerm
        { Object l = DynaTerm.create("\$define_term", DynaTerm.create_arr($a.t, $p.args), $agg.t, $t.rterm);
              if($rterm == null) $rterm = l;
              else { $rterm = DynaTerm.create(",", $rterm, l);  }
        }
    |
        (dbase=expression '.'  {$dbase_rterm = $dbase.rterm;  assert(false);})?
        a=atom
      p=parameters EndTerm
      {
            // writing `a(1,2,3).` is just a short hand for `a(1,2,3) :- true.`
            $rterm = DynaTerm.create("\$define_term", DynaTerm.create_arr($a.t, $p.args), ":-", DynaTerm.create("\$constant", true));
      }
    // queries
    | query EndQuery {
                      assert(false); // todo
        }
    // compiler statements
    // | ':-' ce=compilerExpression EndTerm { $trm = $ce.trm; $prog.addTerm($trm); }
    // assert is something that if it fails, then it can report an error all of the way back to the user.  There should be no calling dynabase in this case
    | 'assert'
        t=termBody EndTerm
        {
            $rterm = DynaTerm.create("\$define_term", DynaTerm.create("\$assert"), "assert", $t.rterm);
        }
// there could be warnings if some library is used in a particular way.  This should somehow defer in the case that some dynabase has not been constructed, but this would want to have that the expression would later come into existence
    | 'warning' '(' we=expression ')' t=termBody EndTerm
    ;


termBody returns[Object rterm]
      locals [
         Object with_key=null
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
      (withKey {$with_key = $withKey.rterm;})?
        (fe=forExpr {
            // the for expression is something that would be the same as just placing it first in the common expression
                $rterm = DynaTerm.create(",", $fe.rterm, $rterm);
            })?
      {
        if($with_key != null) {
            $rterm = DynaTerm.create("\$with_key", $rterm, $with_key);
        }
      }
    ;

query returns []
      locals [String dname=null, boolean streaming=false]
    : // (name=readAtom (':::' 'streaming' {$streaming=true;})? ':::' {$dname=$name.t;})? e2=expression
      // {
      //   $trm = new QueryNode($e2.trm, $e2.ctx.getSourceInterval(), _input.getText($e2.ctx.getSourceInterval()), $dname, $streaming);
      // }
        'asdfasdfasdfasdf'
    ;

withKey returns [Object rterm]
    : 'arg' e=expression { $rterm = $e.rterm; }
    ;

forExpr returns [Object rterm=null]
    : 'for' (e=expression Comma {
        if($rterm == null) { $rterm = $e.rterm; }
        else { $rterm = DynaTerm.create(",", $rterm, $e.rterm); }
    })* e=expression {
        if($rterm == null) { $rterm = $e.rterm; }
        else { $rterm = DynaTerm.create(",", $rterm, $e.rterm); }
    }
    ;

parameters returns [ArrayList<Object> args]
    :/* empty */ { $args = new ArrayList<>(); }
    | '(' p=arguments ')' { $args = $p.args; }
    | '(' ')' { $args = new ArrayList<>(); }
    ;

methodName returns [String name]
    : r=readAtom {$name = $r.t;}
    ;

methodCall returns [String name, ArrayList<Object> args]
    : m=methodName '(' a=arguments ')'
    {
       $name = $m.name;
       $args = $a.args;
    }
    | m=methodName
    {
      $name = $m.name;
      $args = new ArrayList<>();
    }
    ;


// we could have something like $atoms will just quote their arguments so it
// would be something like a macro a bit, where those somehow expand out more.
// This is the approach that julia takes for its macros.
// there is also the name!() syntax used in rust for macros.  So this would not be without precident.  If there was something dt

// methodCall2[DynaParserInterface prog] returns[String name, ArrayList<Object>
// args] : m=methodName {$m.getText().startswith("$")}? '(' a=arguments[$prog]
// ')' | m=methodName {false}? '(' a=arguments[$prog] ')' ;



arguments returns [ArrayList<Object> args = new ArrayList<>();]
    : (e=expression Comma {$args.add($e.rterm);})* e=expression {$args.add($e.rterm);}
    ;

array returns [Object rterm] locals []
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

arrayElements returns [ArrayList<Object> elems = new ArrayList<>(); ]
    : (e=expression Comma {$elems.add($e.rterm);})* e=expression {$elems.add($e.rterm);} Comma?
    ;

assocativeMap returns[Object rterm] locals []
    : '{' '}'   { $rterm = DynaTerm.create("\$map_empty"); }
    | '{' a=assocativeMapElements '}'
        {
            $rterm = DynaTerm.create("\$map_empty");
            for(SimplePair<Object,Object> p : $a.elements) {
                $rterm = DynaTerm.create("\$map_element", p.a, p.b, $rterm);
            }
        }
    | '{' a=assocativeMapElements '|' b=expression '}'
        {
            $rterm = $b.rterm;
            for(SimplePair<Object,Object> p : $a.elements) {
                $rterm = DynaTerm.create("\$map_element", p.a, p.b, $rterm);
            }
        }
    ;

assocativeMapElements returns[ArrayList<SimplePair<Object,Object>> elements = new ArrayList<>();]
    : (a=assocativeMapElement Comma {$elements.add(new SimplePair($a.key, $a.value));} )*
        a=assocativeMapElement {$elements.add(new SimplePair($a.key, $a.value));} Comma?
    ;

assocativeMapElement returns[Object key, Object value]
    : v=Variable { $key = DynaTerm.create("\$constant", $v.getText()); $value = DynaTerm.create("\$variable", $v.getText()); }
    | a=expression '->' b=expression {$key=$a.rterm; $value=$b.rterm;}
    ;


// there could be some syntax for specifying which variables are captured.  This would have that there are some expressions with
dynabase returns[Object rterm]
    locals [ArrayList<Object> terms = new ArrayList<>(), Object par = null]
    : 'new'
        (parent=expression {$par = $parent.rterm;})? // if this inherits from some other dynabase
        {$terms.add($par != null ? $par : DynaTerm.null_term);}
        ('{' (t=term {$terms.add($t.rterm);})* '}')?  // any terms which are defined inside of this dynabase
        {$rterm = DynaTerm.create_arr("\$dynabase_create",  $terms);}
    | {$terms.add(DynaTerm.null_term);} // indicate that there is no dynabase which is the parent of this
      '{' (t=term {$terms.add($t.rterm);})+ '}'
        {$rterm = DynaTerm.create_arr("\$dynabase_create",  $terms);}
    ;

////////////////////

// inlineAggregatedBody[DynaParserInterface prog] returns [Object value]
//     locals [ArrayList<ParseNode> exprList = new ArrayList<>();]
//     : (e=expression[$prog] Comma {$exprList.add($e.trm);})* e=expression {$exprList.add($e.trm);}
//       { $trm = CommaOperatorNode.make($exprList); }
//     ;

// inlineAggregatedBodies returns [ArrayList<ParseNode> bodies = new ArrayList<>();]
//     : (a=inlineAggregatedBody ';' {$bodies.add($a.trm);})* a=inlineAggregatedBody {$bodies.add($a.trm);}
//     ;


inlineAggregated returns [Object value]
    : '(' agg=aggregatorName
        {assert(false);}
        (termBody ';')*
        termBody
        ')'
    ;

inlineAnnonFunction returns [Object value]
locals [ArrayList<String> varlist = new ArrayList<>()]
    : '(' (v=Variable Comma {$varlist.add($v.getText());} )* v=Variable {$varlist.add($v.getText());} '~>'
    {
    assert(false);
    }
    termBody
{
    assert(false);
    // this wants to get a reference to the annon function, not call it immediately.
    // so this should construct what the name for the item is, but not identify which of the arguments
}
')'
    ;






// this is apparently the suggested way to deal with order of operators in antlr
expressionRoot returns [Object rterm]
    : m=methodCall { $rterm = DynaTerm.create_arr($m.name, $m.args); }
    | '&' m=methodCall {
          $rterm = DynaTerm.create("\$quote1", DynaTerm.create_arr($m.name, $m.args)); }
    | '&' dbase=expression '.' m=methodCall {
            assert(false);
            // this is something like constructing, or deconstructing a structured term in a specific dynabase
        }
    | v=Variable {
            if($v.getText().equals("_")) {
                $rterm = DynaTerm.create("\$annon_variable");  // these are variables which can not be referenced in more than once place by name
            } else {
                $rterm = DynaTerm.create("\$variable", $v.getText());
            }
      }
    | primitive { $rterm = DynaTerm.create("\$constant", $primitive.v); }
    | inlineAggregated { assert(false); }
        // | '(' agg=aggregatorName ia=inlineAggregatedBodies')'
    //   {
    //     $trm = new InlinedAggregatedExpression($agg.t, $ia.bodies);
    //   }
    | '(' e=expression ')' { $rterm = $e.rterm; }
    | a=array { $rterm = $a.rterm; }
    | ':' m=methodCall {  // for supporthing things like f(:int) => f(_:int)
            $rterm = DynaTerm.create("\$varible", DynaTerm.gensym_variable_name());
            $m.args.add($rterm);
            $rterm = DynaTerm.create(",", DynaTerm.create($m.name, $m.args), $rterm); }
    | mp=assocativeMap { $rterm=$mp.rterm; }
    | db=dynabase { $rterm = $db.rterm; }
    //| dba=dynabaseAccess[$prog] { $rterm = $dba.rterm; }
    | '*' v=Variable '(' arguments ')' {
            // for doing an indirect call to some value
            $arguments.args.add(0, DynaTerm.create("\$variable", $v.getText()));
            $rterm = DynaTerm.create_arr("\$call", $arguments.args);
        }
    ;

expressionTyped returns [Object rterm]
    : a=expressionRoot {$rterm=$a.rterm;}
    | a=expressionRoot ':' b=methodCall {
            $b.args.add($a.rterm);
            $rterm = DynaTerm.create(",", DynaTerm.create_arr($b.name, $b.args), $a.rterm);
      } // this is going to ahve to add some method call to the value of the statement
    ;

expressionDynabaseAccess returns[Object rterm]
    : a=expressionTyped {$rterm=$a.rterm;} ('.' m=methodCall {$rterm = DynaTerm.create("\$dynabase_call", $rterm, DynaTerm.create_arr($m.name, $m.args));})*
    ;


expressionUnaryMinus returns [Object rterm]
    : b=expressionDynabaseAccess {$rterm = $b.rterm;}
    | '-' b=expressionDynabaseAccess {$rterm = DynaTerm.create("\$unary_-", $b.rterm);}
    ;

expressionExponent returns [Object rterm]
    : b=expressionUnaryMinus {$rterm = $b.rterm;}
    | a=expressionUnaryMinus '**' b=expressionUnaryMinus {$rterm = DynaTerm.create("**", $a.rterm, $b.rterm);}
    ;

expressionMulicative returns [Object rterm]
    : a=expressionExponent {$rterm = $a.rterm;} (op=('*'|'/'|'//') b=expressionExponent
                {$rterm = DynaTerm.create($op.getText(), $rterm, $b.rterm);})*
    ;

// expressionMulicative returns [Object rterm]
//     locals [Object pvalue = null, String prev_op  = null;]
//     : (a=expressionExponent[$prog] op=('*'|'/'|'//')
//          {
//            if($pvalue != null) {
//                $pvalue = $prog.make_call($prev_op, new Object[]{$pvalue, $a.value});
//            } else {
//                $pvalue = $a.value;
//            }
//            $prev_op = $op.getText();
//          })* b=expressionExponent[$prog] {
//             if($pvalue != null) {
//                 $value = $prog.make_call($prev_op, new Object[]{$pvalue, $b.value});
//             } else {
//                 $value = $b.value;
//             }
//          }
//     ;

expressionAdditive returns [Object rterm]
    : a=expressionMulicative {$rterm = $a.rterm;} (op=('+'|'-') b=expressionMulicative
            {$rterm = DynaTerm.create($op.getText(), $rterm, $b.rterm);})*
    ;

// expressionAdditive[DynaParserInterface prog] returns [Object value]
//     locals [Object pvalue = null, String prev_op  = null;]
//     : (a=expressionMulicative[$prog] op=('+'|'-')
//             {
//            if($pvalue != null) {
//                $pvalue = $prog.make_call($prev_op, new Object[]{$pvalue, $a.value});
//            } else {
//                $pvalue = $a.value;
//            }
//            $prev_op = $op.getText();
//          })* b=expressionMulicative[$prog] {
//             if($pvalue != null) {
//                 $value = $prog.make_call($prev_op, new Object[]{$pvalue, $b.value});
//             } else {
//                 $value = $b.value;
//             }
//          }
//     ;

expressionRelationCompare returns [Object rterm]
    : b=expressionAdditive {$rterm = $b.rterm;}
    | a=expressionAdditive op=('>'|'<'|'<='|'>=') b=expressionAdditive
        {$rterm= DynaTerm.create($op.getText(), $a.rterm, $b.rterm);}
    ;

expressionEqualsCompare returns [Object rterm]
    : a=expressionRelationCompare {$rterm = $a.rterm;}
        (op=('=='|'!=') b=expressionRelationCompare
            {$rterm = DynaTerm.create($op.getText(), $rterm, $b.rterm);})*
    ;

// expressionEqualsCompare returns [Object rterm]
//     locals [Object pvalue = null, String prev_op  = null;]
//     : (a=expressionRelationCompare[$prog] op=('=='|'!=')
//         {
//            if($pvalue != null) {
//                $pvalue = $prog.make_call($prev_op, new Object[]{$pvalue, $a.value});
//            } else {
//                $pvalue = $a.value;
//            }
//            $prev_op = $op.getText();
//          })* b=expressionRelationCompare[$prog] {
//             if($pvalue != null) {
//                 $value = $prog.make_call($prev_op, new Object[]{$pvalue, $b.value});
//             } else {
//                 $value = $b.value;
//             }
//          }
//     ;

expressionLogical returns [Object rterm]
    : a=expressionEqualsCompare {$rterm = $a.rterm;}
        (op=('||'|'&&') b=expressionEqualsCompare
            {$rterm = DynaTerm.create($op.getText(), $rterm, $b.rterm);})*
    ;

// expressionLogical[DynaParserInterface prog] returns [Object value]
//     locals [Object pvalue = null, String prev_op  = null;]
//     : (a=expressionEqualsCompare[$prog] op=('||'|'&&')
//         {
//            if($pvalue != null) {
//                $pvalue = $prog.make_call($prev_op, new Object[]{$pvalue, $a.value});
//            } else {
//                $pvalue = $a.value;
//            }
//            $prev_op = $op.getText();
//          })* b=expressionEqualsCompare[$prog] {
//             if($pvalue != null) {
//                 $value = $prog.make_call($prev_op, new Object[]{$pvalue, $b.value});
//             } else {
//                 $value = $b.value;
//             }
//          }
//     ;

expressionIs returns [Object rterm]
    : a=expressionLogical {$rterm=$a.rterm;}
    | a=expressionLogical ('is'|'=') b=expressionLogical
        {$rterm = DynaTerm.create("\$unify", $a.rterm, $b.rterm);}
    ;

expression returns [Object rterm]
    : a=expressionIs { $rterm = $a.rterm; }
    ;

// // expressions which change how the parser behaves or how the runtime works for given expression
// compilerExpression returns [ParseNode trm]
//     : 'dispos' disposeAnnotation { $trm = $disposeAnnotation.trm; }
//     | 'dynabase_auto' '(' onOffArgument ')' { $trm = new FeatureEnable("dynabase_auto", $onOffArgument.t); }
//     | 'allow_dollar_define' '(' onOffArgument ')' { $trm = new FeatureEnable("allow_dollar_define", $onOffArgument.t); }
//     | 'allow_define' '(' methodId Comma  onOffArgument ')' { $trm = new FeatureEnable("allow_define_"+$methodId.name+"/"+$methodId.n, $onOffArgument.t); }
//     | 'dispos_auto_quote' '(' onOffArgument ')' { $trm = new FeatureEnable("dispos_auto_quote", $onOffArgument.t); }
//     | 'allow_ir_expressions' '(' onOffArgument ')' { $trm = new FeatureEnable("allow_ir_expressions", $onOffArgument.t); }
//     | 'auto_allocate_variables' '(' onOffArgument ')' { $trm = new FeatureEnable("auto_allocate_variables", $onOffArgument.t); }
//     | 'auto_iterate_variables' '(' onOffArgument ')' { $trm = new FeatureEnable("auto_iterate_variables", $onOffArgument.t); }
//     | 'import' f=stringConst { $trm = new ImportOtherFile($f.t); }
//     | 'forward_chained' methodId { $trm = new ForceMethodMode("forward_chained", $methodId.name, $methodId.n); }
//     | 'force_backwards' methodId { $trm = new ForceMethodMode("force_backwards", $methodId.name, $methodId.n); }
//     | 'memoized_default_unk' methodId { $trm = new ForceMethodMode("memoized_default_unk", $methodId.name, $methodId.n); }
//     | 'memoized_default_null' methodId { $trm = new ForceMethodMode("memoized_default_null", $methodId.name, $methodId.n); }
//     | 'parameter_container' methodId { $trm = new ForceMethodMode("parameter_container", $methodId.name, $methodId.n); }
//     | 'never_optimize_as_constant' methodId { $trm = new FeatureEnable("never_optimize_constant_load_"+$methodId.name+"/"+$methodId.n, true); }
//     | 'dump_memotable_at_end' methodId { $trm = new ForceMethodMode("dump_memotable_at_end", $methodId.name, $methodId.n); }
//     | 'delete_all' methodId { $trm = new ForceMethodMode("delete_term", $methodId.name, $methodId.n); }
//     ;

// disposeAnnotation returns [ParseNode trm]
// locals [ArrayList<String> args = new ArrayList<>();]
//     : self=('*'|'&')? n=methodName ('(' (ar=disposeArgument Comma { $args.add($ar.t); } )* ar=disposeArgument { $args.add($ar.t); } ')' )?
//       { $trm = new DisposExpression($n.name, $self.getText(), $args); }
//     ;

// disposeArgument returns [String t]
//     : '*' { $t = "*"; }
//     | '&' { $t = "&"; }
// //    | '$quote' { $t = "$quote"; }  // TODO remove. this isn't actually going to be used any more (I think
//     ;

onOffArgument returns [boolean t]
    : 'on' { $t = true; }
    | 'off' { $t = false; }
    ;

methodId returns [String name, int n]
    : a=atom '/' b=NumberInt { $name = $a.t; $n = java.lang.Integer.valueOf($b.getText()); }
    ;
