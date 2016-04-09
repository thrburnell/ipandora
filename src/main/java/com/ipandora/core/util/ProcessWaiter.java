package com.ipandora.core.util;

import java.util.concurrent.Callable;

/**
 * A Callable that waits for the completion of a Process, before returning its exit code.
 */
public class ProcessWaiter implements Callable<Integer> {

    private final Process process;

    public ProcessWaiter(Process process) {
        this.process = process;
    }

    @Override
    public Integer call() throws InterruptedException {
        return process.waitFor();
    }

}
