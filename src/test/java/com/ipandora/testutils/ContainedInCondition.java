package com.ipandora.testutils;

import org.assertj.core.api.Condition;

import java.util.Arrays;
import java.util.List;

public class ContainedInCondition<T> extends Condition<T> {

    private List<T> values;

    public ContainedInCondition(T... ts) {
        this.values = Arrays.asList(ts);
    }

    @Override
    public boolean matches(T t) {
        return values.contains(t);
    }

}
