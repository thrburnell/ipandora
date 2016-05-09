package com.ipandora.api.predicate.term;

import com.ipandora.core.term.TermVisitor;

import java.util.List;

public class Function implements Term {

    private final String name;
    private final List<Term> args;

    public Function(String name, List<Term> args) {
        this.name = name;
        this.args = args;
    }

    public String getName() {
        return name;
    }

    public List<Term> getArgs() {
        return args;
    }

    @Override
    public <T> T accept(TermVisitor<T> visitor) {
        return visitor.visitFunction(this);
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        for (int i = 0; i < args.size(); i++) {
            sb.append(args.get(i));
            if (i < args.size() - 1) {
                sb.append(", ");
            }
        }

        return String.format("%s(%s)", name, sb);
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        Function function = (Function) o;

        if (!name.equals(function.name)) return false;
        return args.equals(function.args);
    }

    @Override
    public int hashCode() {
        int result = name.hashCode();
        result = 31 * result + args.hashCode();
        return result;
    }

}
