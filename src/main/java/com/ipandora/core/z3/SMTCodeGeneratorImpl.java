package com.ipandora.core.z3;

import com.ipandora.api.predicate.formula.Formula;
import com.ipandora.api.predicate.function.FunctionPrototype;
import com.ipandora.api.predicate.formula.PredicatePrototype;
import com.ipandora.api.predicate.term.Type;
import com.ipandora.api.predicate.term.TypeMismatchException;
import com.ipandora.core.util.Creator;
import com.ipandora.core.util.WrappingRuntimeException;
import org.apache.commons.lang3.StringUtils;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Set;

public class SMTCodeGeneratorImpl implements SMTCodeGenerator {

    private final Creator<SMTGeneratingFormulaVisitor> visitorCreator;

    public SMTCodeGeneratorImpl(Creator<SMTGeneratingFormulaVisitor> visitorCreator) {
        this.visitorCreator = visitorCreator;
    }

    @Override
    public String generateCheckSatCode(Formula formula) throws Z3InvalidProblemException {

        StringBuilder sb = new StringBuilder();
        SMTGeneratingFormulaVisitor visitor = visitorCreator.create();
        String formulaCode;

        try {
            formulaCode = visitor.visit(formula);
        } catch (WrappingRuntimeException wre) {
            // Catch type mismatch errors and throw checked exception; let others propagate as RuntimeExceptions
            Exception wrapped = wre.getWrappedException();
            if (wrapped instanceof TypeMismatchException) {
                throw new Z3InvalidProblemException("Invalid formula: " + wrapped.getMessage());
            }
            throw wre;
        }

        appendTypeDefinition(sb);
        appendPredicateDefinitions(visitor.getPredicatePrototypes(), sb);
        appendPropositionDefinitions(visitor.getPropositionNames(), sb);
        appendConstantDefinitions(visitor.getConstantNamesToTypes(), sb);
        appendFunctionDefinitions(visitor.getFunctionPrototypes(), sb);

        sb.append("(assert ").append(formulaCode).append(") (check-sat)");

        return sb.toString();
    }

    private StringBuilder appendTypeDefinition(StringBuilder sb) {
        return sb.append("(declare-sort ").append(Z3Sort.ARBITRARY.getCode()).append(")");
    }

    private StringBuilder appendPredicateDefinitions(List<PredicatePrototype> predicatePrototypes,
                                                     StringBuilder sb) {

        for (PredicatePrototype prototype : predicatePrototypes) {
            String args = getZ3SortParamString(prototype.getArgTypes());
            sb.append(String.format("(declare-fun %s (%s) %s)\n", prototype.getName(), args, Z3Sort.BOOL.getCode()));
        }

        return sb;
    }

    private StringBuilder appendPropositionDefinitions(Set<String> propositionNames, StringBuilder sb) {

        for (String proposition : propositionNames) {
            sb.append(String.format("(declare-const %s %s)", proposition, Z3Sort.BOOL.getCode()));
        }

        return sb;
    }

    private StringBuilder appendConstantDefinitions(Map<String, Type> constantNamesToTypes, StringBuilder sb) {

        for (Map.Entry<String, Type> constant : constantNamesToTypes.entrySet()) {
            String name = constant.getKey();
            Type type = constant.getValue();
            String typeCode = Z3Sort.forType(type).getCode();
            sb.append(String.format("(declare-const %s %s)", name, typeCode));
            if (type == Type.NAT) {
                sb.append(String.format("(assert (>= %s 0))", name));
            }
        }

        return sb;
    }

    private StringBuilder appendFunctionDefinitions(List<FunctionPrototype> functionPrototypes, StringBuilder sb) {

        for (FunctionPrototype prototype : functionPrototypes) {
            String name = prototype.getName();
            String args = getZ3SortParamString(prototype.getArgTypes());
            Type returnType = prototype.getReturnType();
            String returnTypeStr = Z3Sort.forType(returnType).getCode();
            sb.append(String.format("(declare-fun %s (%s) %s)", name, args, returnTypeStr));

            if (returnType == Type.NAT) {
                appendFunctionReturnValueNatGuard(prototype, sb);
            }
        }

        return sb;
    }

    private void appendFunctionReturnValueNatGuard(FunctionPrototype prototype, StringBuilder sb) {
        assert prototype.getReturnType() == Type.NAT;

        // appends an assertion such as:
        // (assert (forall ((x0 Int)(x1 Type)(x2 Int)) (>= (f x0 x1 x2) 0)))

        final String FUNCTION_ARG_NAME_BASE = "x";
        String name = prototype.getName();
        List<Type> argTypes = prototype.getArgTypes();

        sb.append("(assert (forall (");

        for (int i = 0; i < argTypes.size(); i++) {
            sb.append("(").append(FUNCTION_ARG_NAME_BASE).append(i).append(" ")
                    .append(Z3Sort.forType(argTypes.get(i)).getCode()).append(")");
        }

        sb.append(") (>= (");
        sb.append(name);

        for (int i = 0; i < argTypes.size(); i++) {
            sb.append(" ");
            sb.append(FUNCTION_ARG_NAME_BASE).append(i);
        }

        sb.append(") 0)))");
    }

    private String getZ3SortParamString(List<Type> types) {
        List<String> z3Types = new ArrayList<>();
        for (Type type : types) {
            z3Types.add(Z3Sort.forType(type).getCode());
        }

        return StringUtils.join(z3Types, " ");
    }

}
