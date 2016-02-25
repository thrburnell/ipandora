package com.ipandora.resources;

import com.ipandora.api.predicate.FormulaString;
import com.ipandora.core.FormulaBuildingVisitor;
import com.ipandora.parser.PredicateLogicLexer;
import com.ipandora.parser.PredicateLogicParser;
import org.antlr.v4.runtime.ANTLRInputStream;
import org.antlr.v4.runtime.CommonTokenStream;

import javax.ws.rs.Consumes;
import javax.ws.rs.POST;
import javax.ws.rs.Path;
import javax.ws.rs.Produces;
import javax.ws.rs.core.MediaType;

@Path("/")
@Produces(MediaType.APPLICATION_JSON)
@Consumes(MediaType.APPLICATION_JSON)
public class FormulaResource {

    @POST
    public FormulaString stringifyFormula(FormulaString formulaString) {
        String formula = formulaString.getFormula();
        ANTLRInputStream stream = new ANTLRInputStream(formula);
        PredicateLogicLexer lexer = new PredicateLogicLexer(stream);
        CommonTokenStream tokens = new CommonTokenStream(lexer);
        PredicateLogicParser parser = new PredicateLogicParser(tokens);
        PredicateLogicParser.FormulaContext formulaCtx = parser.formula();
        FormulaBuildingVisitor visitor = new FormulaBuildingVisitor();

        return new FormulaString(visitor.visit(formulaCtx).toString());
    }

}
