/*
 *   Project: Speedith.Core
 * 
 * File name: ParseException.java
 *    Author: Matej Urbas [matej.urbas@gmail.com]
 * 
 *  Copyright © 2011 Matej Urbas
 * 
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 * 
 * The above copyright notice and this permission notice shall be included in
 * all copies or substantial portions of the Software.
 * 
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
 * THE SOFTWARE.
 */

package speedith.core.lang.reader;

import org.antlr.runtime.BaseRecognizer;
import org.antlr.runtime.RecognitionException;

import static speedith.core.i18n.Translations.i18n;

/**
 * This exception is thrown upon a parsing error.
 * <p>An exception of this type indicates that the input (the textual
 * representation of the spider diagram) uses an invalid syntax.</p>
 * @author Matej Urbas [matej.urbas@gmail.com]
 */
public class ParseException extends RuntimeException {

    // <editor-fold defaultstate="collapsed" desc="Fields">
    private BaseRecognizer origin;
    // </editor-fold>

    // <editor-fold defaultstate="collapsed" desc="Constructors">
    /**
     * Initialises an instance of the {@link ParseException} class.
     * <p>It takes a description of the exception (usually a syntax error on the
     * user's side) and the detailed description of the syntax error (an
     * instance of the ANTLR's {@link RecognitionException} class).</p>
     * <p>For a detailed description of the {@code RecognitionException} class
     * see the
     * <a href="http://www.antlr.org/api/Java/classorg_1_1antlr_1_1runtime_1_1_recognition_exception.html">ANTLR Java Runtime API Documentation</a>.</p>
     * @param description the string describing the syntax error.
     * @param ex the class which contains detailed information on what went
     * wrong during parsing (can be used to give feedback to the user, see the <a href="http://www.antlr.org/depot/antlr3/release-3.2/runtime/Java/src/main/java/org/antlr/runtime/BaseRecognizer.java">source of the {@code BaseRecognizer} class</a>,
     * specifically the method {@code displayRecognitionError} on how to do this).
     * @param origin the recogniser (either the parser or the lexer) that has
     * thrown the exception.
     */
    public ParseException(String description, RecognitionException ex, BaseRecognizer origin) {
        super(description, ex);
        if (ex == null) {
            throw new IllegalArgumentException(i18n("GERR_NULL_ARGUMENT", "ex"));
        }
        if (origin == null) {
            throw new IllegalArgumentException(i18n("GERR_NULL_ARGUMENT", "origin"));
        }
        this.origin = origin;
    }
    // </editor-fold>

    // <editor-fold defaultstate="collapsed" desc="Public Methods">
    @Override
    public RecognitionException getCause() {
        return (RecognitionException) super.getCause();
    }

    /**
     * Returns the recogniser (either the parser or the lexer) that has
     * thrown the exception.
     * @return the recogniser (either the parser or the lexer) that has
     * thrown the exception.
     */
    public BaseRecognizer getOrigin() {
        return origin;
    }
    // </editor-fold>
}
