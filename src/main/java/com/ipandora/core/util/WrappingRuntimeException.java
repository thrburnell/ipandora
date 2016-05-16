package com.ipandora.core.util;

/**
 * A RuntimeException used to wrap a Throwable, typically a checked Exception. Handy for use in visitors.
 */
public final class WrappingRuntimeException extends RuntimeException {

    private final Exception wrappedException;

    public WrappingRuntimeException(Exception cause) {
        super(cause);
        this.wrappedException = cause;
    }

    public Exception getWrappedException() {
        return wrappedException;
    }

}
