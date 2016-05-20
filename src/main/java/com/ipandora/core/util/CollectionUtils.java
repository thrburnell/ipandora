package com.ipandora.core.util;

import java.util.*;

public class CollectionUtils {

    public static <T> List<T> extractMapValues(Map<?, T> map) {
        ArrayList<T> values = new ArrayList<>();
        for (Map.Entry<?, T> entry : map.entrySet()) {
            values.add(entry.getValue());
        }
        return values;
    }

    public static <T extends V, V, C extends Collection<V>> C flatten(
            Collection<? extends Collection<T>> lists, C result) {

        for (Collection<T> subList : lists) {
            result.addAll(subList);
        }
        return result;
    }

}
