// antlr4 grammar for dyna



// some bug that prevents us from having this loaded in a package
// looks like it might be how the build script is trying to locate items
// also unable to use any additional tools from antlr when using a package name...lame
grammar dyna_grammar;
//
@header {
package dyna_backend;//.genparser;

import dyna_backend.DynaParserInterface;
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

junk3: ;

// if we want to support multilined strings in the future or something, we can just do that here
stringConst returns[String t] locals [String vv]
    : a=StringConst { $vv = $a.getText(); $t = $vv.substring(1, $vv.length() - 1); }
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



program [DynaParserInterface prog]
// @init {
//   // based of antlr4 book p184
//   //$prog = new DynaProgram();
// }
    : (term[$prog]
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
        }
      )* EOF
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


term [DynaParserInterface prog]
     returns[]
    locals [DynaParserInterface lprog]
    : a=atom p=parameters[$prog] agg=aggregatorName
        {$prog.set_atom($a.t, $p.args, $agg.t); }
      ({$lprog = (DynaParserInterface)$prog.copy_interface(); }
            termBody[$lprog] ';')*
        termBody[$prog] EndTerm
    | a=atom p=parameters[$prog] EndTerm
      {
            // writing `a(1,2,3).` is just a short hand for `a(1,2,3) :- true.`
            $prog.set_atom($a.t, $p.args, ":-");
            // there needs to be some construct atom rule with the current cojuncts and something which takes the current value for an expression
            $prog.construct_atom($prog.make_constant(true));
      }
    // queries
    | query EndQuery {

        }
    // compiler statements
    // | ':-' ce=compilerExpression EndTerm { $trm = $ce.trm; $prog.addTerm($trm); }
    // assert statement check at the end of a transaction
    | 'assert'
      {$prog.set_atom("assert", new Object[]{}, "assert=");}
      termBody[$prog]
    ;


termBody[DynaParserInterface prog] returns[]
      locals [
         Object with_key=null,
         Object result_value = null;
      ]
    : (e=expression[$prog] Comma { $prog.unify_with_true($e.value); })* e2=expression[$prog]
      (withKey[$prog] {$with_key = $withKey.value;})?
      forExpr[$prog]?
      {
            $result_value = $e2.value;
            if($with_key != null) {
                $result_value = $prog.make_structure("\$with_key_pair", new Object[]{$with_key, $result_value});
            }
            $prog.construct_atom($result_value);
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

withKey[DynaParserInterface prog] returns [Object value]
    : 'arg' e=expression[$prog] { $value = $e.value; }
    ;

forExpr[DynaParserInterface prog]
    : 'for' (e=expression[$prog] Comma {$prog.unify_with_true($e.value);})* e=expression[$prog] {$prog.unify_with_true($e.value);}
    ;

parameters[DynaParserInterface prog]
          returns [ArrayList<Object> args]
    :/* empty */ { $args = new ArrayList<>(); }
    | '(' p=arguments[$prog] ')' { $args = $p.args; }
    | '(' ')' { $args = new ArrayList<>(); }
    ;
//
//parameterList returns [ArrayList<ParseNode> args]
//    : {$args = new ArrayList<>();} (p=parameter Comma {$args.add($p.trm);})* p=parameter {$args.add($p.trm);}
//    ;
//
//parameter returns [ParseNode trm]
//    : e=expression { $trm = $e.trm; }
//    ;

methodName returns [String name]
    : r=readAtom {$name = $r.t;}
    ;

methodCall[DynaParserInterface prog] returns [String name, ArrayList<Object> args]
    : m=methodName '(' a=arguments[$prog] ')'
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

arguments[DynaParserInterface prog]
         returns [ArrayList<Object> args = new ArrayList<>();]
    : (e=expression[$prog] Comma {$args.add($e.value);})* e=expression[$prog] {$args.add($e.value);}
    ;

array[DynaParserInterface prog] returns [Object value] locals []
    : '[' elems=arrayElements[$prog] ']'  { assert(false); }
    | '[' elems=arrayElements[$prog] '|' t=expression[$prog] ']' { assert(false); }
    | '[' ']' { assert(false); }
    ;

arrayElements[DynaParserInterface prog] returns [ArrayList<Object> elems = new ArrayList<>(); ]
    : (e=expression[$prog] Comma {$elems.add($e.value);})* e=expression[$prog] {$elems.add($e.value);}
    ;

////////////////////

// inlineAggregatedBody[DynaParserInterface prog] returns [Object value]
//     locals [ArrayList<ParseNode> exprList = new ArrayList<>();]
//     : (e=expression Comma {$exprList.add($e.trm);})* e=expression {$exprList.add($e.trm);}
//       { $trm = CommaOperatorNode.make($exprList); }
//     ;

// inlineAggregatedBodies returns [ArrayList<ParseNode> bodies = new ArrayList<>();]
//     : (a=inlineAggregatedBody ';' {$bodies.add($a.trm);})* a=inlineAggregatedBody {$bodies.add($a.trm);}
//     ;

expressionRoot[DynaParserInterface prog] returns [Object value]
    : m=methodCall[$prog] { $value = $prog.make_call($m.name, $m.args); }
    | '&' m=methodCall[$prog] { $value = $prog.make_structure($m.name, $m.args); }

    | v=Variable { $value = $prog.make_variable($v.getText()); }
    | primitive { $value = $prog.make_constant($primitive.v); }
    // | '(' agg=aggregatorName ia=inlineAggregatedBodies')'
    //   {
    //     $trm = new InlinedAggregatedExpression($agg.t, $ia.bodies);
    //   }
    | '(' e=expression[$prog] ')' { $value = $e.value; }
    | a=array[$prog] { $value = $a.value; }
    | ':' m=methodCall[$prog] {  // for supporthing things like f(:int) => f(_:int)
            $value = $prog.make_unnamed_variable();
            $m.args.add($value);
            $prog.unify_with_true($prog.make_call($m.name, $m.args)); }
    ;

expressionTyped[DynaParserInterface prog] returns [Object value]
    : a=expressionRoot[$prog] {$value=$a.value;}
    | a=expressionRoot[$prog] ':' b=methodCall[$prog] {
            $value = $a.value;
            $b.args.add($value);
            $prog.unify_with_true($prog.make_call($b.name, $b.args));
            assert(false); } // this is going to ahve to add some method call to the value of the statement
    ;

// this is apparently the suggested way to deal with order of operators in antlr

expressionUnaryMinus[DynaParserInterface prog] returns [Object value]
    : b=expressionTyped[$prog] {$value = $b.value;}
    | '-' b=expressionTyped[$prog] {$value = $prog.make_call("unary_-", new Object[]{$b.value});}
    ;

expressionExponent[DynaParserInterface prog] returns [Object value]
    : b=expressionUnaryMinus[$prog] {$value=$b.value;}
    | a=expressionUnaryMinus[$prog] '**' b=expressionUnaryMinus[$prog] {$value = $prog.make_call("**", new Object[]{$a.value, $b.value});}
    ;

expressionMulicative[DynaParserInterface prog] returns [Object value]
    locals [Object pvalue = null, String prev_op  = null;]
    : (a=expressionExponent[$prog] op=('*'|'/'|'//')
         {
           if($pvalue != null) {
               $pvalue = $prog.make_call($prev_op, new Object[]{$pvalue, $a.value});
           } else {
               $pvalue = $a.value;
           }
           $prev_op = $op.getText();
         })* b=expressionExponent[$prog] {
            if($pvalue != null) {
                $value = $prog.make_call($prev_op, new Object[]{$pvalue, $b.value});
            } else {
                $value = $b.value;
            }
         }
    ;

// expressionMulicative[DynaParserInterface prog] returns [Object value]
//     : a=expressionMulicative[$prog] op=('*'|'/'|'//') b=expressionExponent[$prog]
//         {$value = $prog.make_call($op.getText(), new Object[]{$a.value, $b.value});}
//     | b=expressionExponent[$prog] {$value=$b.value;}
//     ;

expressionAdditive[DynaParserInterface prog] returns [Object value]
    locals [Object pvalue = null, String prev_op  = null;]
    : (a=expressionMulicative[$prog] op=('+'|'-')
            {
           if($pvalue != null) {
               $pvalue = $prog.make_call($prev_op, new Object[]{$pvalue, $a.value});
           } else {
               $pvalue = $a.value;
           }
           $prev_op = $op.getText();
         })* b=expressionMulicative[$prog] {
            if($pvalue != null) {
                $value = $prog.make_call($prev_op, new Object[]{$pvalue, $b.value});
            } else {
                $value = $b.value;
            }
         }
    ;

expressionRelationCompare[DynaParserInterface prog] returns [Object value]
    : b=expressionAdditive[$prog] {$value = $b.value;}
    | a=expressionAdditive[$prog] op=('>'|'<'|'<='|'>=') b=expressionAdditive[$prog]
        {$value = $prog.make_call($op.getText(), new Object[]{$a.value, $b.value});}
    ;

expressionEqualsCompare[DynaParserInterface prog] returns [Object value]
    locals [Object pvalue = null, String prev_op  = null;]
    : (a=expressionRelationCompare[$prog] op=('=='|'!=')
        {
           if($pvalue != null) {
               $pvalue = $prog.make_call($prev_op, new Object[]{$pvalue, $a.value});
           } else {
               $pvalue = $a.value;
           }
           $prev_op = $op.getText();
         })* b=expressionRelationCompare[$prog] {
            if($pvalue != null) {
                $value = $prog.make_call($prev_op, new Object[]{$pvalue, $b.value});
            } else {
                $value = $b.value;
            }
         }
    ;

expressionLogical[DynaParserInterface prog] returns [Object value]
    locals [Object pvalue = null, String prev_op  = null;]
    : (a=expressionEqualsCompare[$prog] op=('||'|'&&')
        {
           if($pvalue != null) {
               $pvalue = $prog.make_call($prev_op, new Object[]{$pvalue, $a.value});
           } else {
               $pvalue = $a.value;
           }
           $prev_op = $op.getText();
         })* b=expressionEqualsCompare[$prog] {
            if($pvalue != null) {
                $value = $prog.make_call($prev_op, new Object[]{$pvalue, $b.value});
            } else {
                $value = $b.value;
            }
         }
    ;

expressionIs[DynaParserInterface prog] returns [Object value]
    : a=expressionLogical[$prog] {$value=$a.value;}
    | a=expressionLogical[$prog] ('is'|'=') b=expressionLogical[$prog]
        {$value = $prog.make_call("\$unify", new Object[]{$a.value, $b.value});}
    ;

expression[DynaParserInterface prog] returns [Object value]
    : a=expressionIs[$prog] { $value = $a.value; }
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
