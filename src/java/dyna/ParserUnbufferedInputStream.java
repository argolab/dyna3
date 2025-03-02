package dyna;

import org.antlr.v4.runtime.UnbufferedCharStream;
import org.antlr.v4.runtime.misc.Interval;

import java.io.InputStream;

/**
 * Circular buffer for the parser.  Allows for bigger input files to be handled
 * rather than having to buffer everything in ram.
 */
public class ParserUnbufferedInputStream extends UnbufferedCharStream {

    public ParserUnbufferedInputStream(InputStream input, int bufferSize) {
        super(input, bufferSize);
    }

    private final int[] oldBuffer = new int[bufferSize];

    @Override
    public void consume() {
       oldBuffer[currentCharIndex % oldBuffer.length] = data[p];
       super.consume();
    }

    @Override
    public String getText(final Interval interval) {
        final int startToken = interval.a;
        final int stopToken = interval.b;

        if(startToken < currentCharIndex - oldBuffer.length || startToken < 0) {
            throw new UnsupportedOperationException("interval " + interval + " outside buffer: " + startToken + ".." + (startToken + this.n - 1));
        }

        int cpy[] = new int[stopToken - startToken + 1];
        int idx = 0;
        for(int i = startToken; i <= stopToken; i++) {
            if(i < currentCharIndex)
                cpy[idx++] = oldBuffer[i % oldBuffer.length];
            else
                cpy[idx++] = data[i - currentCharIndex + p];
        }

        String ret = new String(cpy, 0, cpy.length);
        return ret;
    }

    @Override
    public int size() {
        return currentCharIndex;
    }

    static final int bufferSize = Integer.valueOf(System.getProperty("dyna.parser.bufferSize", "512000"));
}
