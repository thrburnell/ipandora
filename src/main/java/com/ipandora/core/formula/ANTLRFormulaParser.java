package com.ipandora.core.formula;

import com.ipandora.api.predicate.formula.Formula;
import com.ipandora.api.predicate.function.FunctionPrototype;
import com.ipandora.api.predicate.term.TypeMismatchException;
import com.ipandora.core.term.SymbolTable;
import com.ipandora.core.term.SymbolTableCreator;
import com.ipandora.core.term.TermBuildingVisitor;
import com.ipandora.core.util.WrappingRuntimeException;
import com.ipandora.parser.PredicateLogicLexer;
import com.ipandora.parser.PredicateLogicParser;
import org.antlr.v4.runtime.ANTLRInputStream;
import org.antlr.v4.runtime.BailErrorStrategy;
import org.antlr.v4.runtime.CommonTokenStream;
import org.antlr.v4.runtime.misc.ParseCancellationException;

import java.util.Collections;
import java.util.List;

public class ANTLRFormulaParser implements FormulaParser {

    private static final List<FunctionPrototype> EMPTY_LIST = Collections.emptyList();
    private final FormulaTypeChecker formulaTypeChecker;

    public ANTLRFormulaParser(FormulaTypeChecker formulaTypeChecker) {
        this.formulaTypeChecker = formulaTypeChecker;
    }

    @Override
    public Formula fromStringWithTypeChecking(String formula) throws FormulaParsingException {
        return fromStringWithTypeChecking(formula, Collections.<FunctionPrototype>emptyList());
    }

    @Override
    public Formula fromStringWithTypeChecking(String formula, List<FunctionPrototype> functionPrototypes)
            throws FormulaParsingException {

        Formula form = fromString(formula, functionPrototypes);
        try {
            formulaTypeChecker.analyse(form, functionPrototypes);
        } catch (TypeMismatchException e) {
            throw new FormulaParsingException(e);
        }
        return form;
    }

    @Override
    public Formula fromString(String formula) throws FormulaParsingException {
        return fromString(formula, Collections.<FunctionPrototype>emptyList());
    }

    @Override
    public Formula fromString(String formula, List<FunctionPrototype> functionPrototypes)
            throws FormulaParsingException {

        ANTLRInputStream stream = new ANTLRInputStream(formula);
        PredicateLogicLexer lexer = new PredicateLogicLexer(stream);
        CommonTokenStream tokens = new CommonTokenStream(lexer);
        PredicateLogicParser parser = new PredicateLogicParser(tokens);
        parser.setErrorHandler(new BailErrorStrategy());

        PredicateLogicParser.EntireFormulaContext formulaCtx;
        try {
            formulaCtx = parser.entireFormula();
        } catch (ParseCancellationException e) {
            throw new FormulaParsingException("Invalid formula: " + formula);
        }

        SymbolTableCreator stCreator = new SymbolTableCreator();
        SymbolTable rootSymbolTable = populateSymbolTable(stCreator.create(), functionPrototypes);
        FormulaBuildingVisitor formulaBuildingVisitor = makeFormulaBuildingVisitor(rootSymbolTable, stCreator);

        try {
            return formulaBuildingVisitor.visit(formulaCtx);
        } catch (WrappingRuntimeException e) {
            throw new FormulaParsingException(e.getWrappedException());
        }
    }

    private FormulaBuildingVisitor makeFormulaBuildingVisitor(SymbolTable rootSymbolTable,
                                                              SymbolTableCreator symbolTableCreator) {

        TermBuildingVisitor termBuildingVisitor = new TermBuildingVisitor(rootSymbolTable, symbolTableCreator);
        return new FormulaBuildingVisitor(termBuildingVisitor);
    }

    private SymbolTable populateSymbolTable(SymbolTable symbolTable, List<FunctionPrototype> functionPrototypes) {
        for (FunctionPrototype prototype : functionPrototypes) {
            symbolTable.addMapping(prototype.getName(), prototype);
        }
        return symbolTable;
    }

}
