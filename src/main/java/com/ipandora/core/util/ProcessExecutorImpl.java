package com.ipandora.core.util;

import java.io.*;
import java.util.concurrent.*;

public class ProcessExecutorImpl implements ProcessExecutor {

    private final static int INITIAL_BUFFER_LENGTH = 2048;

    @Override
    public String execute(String stdin, int timeoutSeconds, String... command)
            throws IOException, ProcessTimeoutException {

        ExecutorService executorService = Executors.newCachedThreadPool();
        ProcessBuilder processBuilder = new ProcessBuilder(command);

        Process process = processBuilder.start();
        ProcessWaiter processWaiter = new ProcessWaiter(process);
        Future<Integer> statusCodeFuture = executorService.submit(processWaiter);

        ByteArrayInputStream stdinStream = new ByteArrayInputStream(stdin.getBytes());
        StreamCopier inputCopier = new StreamCopier(stdinStream, process.getOutputStream());
        executorService.submit(inputCopier);

        ByteArrayOutputStream stdoutStream = new ByteArrayOutputStream(INITIAL_BUFFER_LENGTH);
        StreamCopier outputCopier = new StreamCopier(process.getInputStream(), stdoutStream);
        Future<?> outputCopierFuture = executorService.submit(outputCopier);

        try {
            statusCodeFuture.get(timeoutSeconds, TimeUnit.SECONDS);
            outputCopierFuture.get();
            return stdoutStream.toString();
        } catch (InterruptedException | ExecutionException e) {
            e.printStackTrace();
            return null;
        } catch (TimeoutException e) {
            throw new ProcessTimeoutException("Process timed out", e);
        } finally {
            executorService.shutdownNow();
        }
    }
}
