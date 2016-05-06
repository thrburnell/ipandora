package com.ipandora.core.term;

import com.ipandora.api.predicate.term.Constant;
import com.ipandora.api.predicate.term.Term;
import com.ipandora.api.predicate.term.Variable;
import com.ipandora.parser.PredicateLogicBaseVisitor;
import com.ipandora.parser.PredicateLogicParser;
import org.antlr.v4.runtime.Token;

public class TermBuildingVisitor extends PredicateLogicBaseVisitor<Term> {
    
    @Override
    public Term visitArg(PredicateLogicParser.ArgContext ctx) {
        Token var = ctx.var;

        if (var != null) {
            return new Variable(var.getText());
        }

        Token constant = ctx.constant;
        return new Constant(constant.getText());
    }
    
}
