package com.ipandora.core.util;

import java.io.*;

/**
 * A Runnable that copies the entire contents of an InputStream to an OutputStream, before flushing and closing the
 * latter.
 */
public class StreamCopier implements Runnable {

    private static final int BUFFER_SIZE_BYTES = 1024;

    private InputStream in;
    private OutputStream out;

    public StreamCopier(final InputStream in, final OutputStream out) {
        this.in = in;
        this.out = out;
    }

    @Override
    public void run() {

        byte[] buffer = new byte[BUFFER_SIZE_BYTES];
        int len;
        try {
            while ((len = in.read(buffer)) != -1) {
                out.write(buffer, 0, len);
            }
        } catch (IOException e) {
            e.printStackTrace();
        } finally {
            try {
                out.flush();
                out.close();
            } catch (IOException e) {
                e.printStackTrace();
            }
        }
    }

}
