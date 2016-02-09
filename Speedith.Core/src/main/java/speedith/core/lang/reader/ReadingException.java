/*
 *   Project: Speedith.Core
 * 
 * File name: ReadingException.java
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

import org.antlr.runtime.MissingTokenException;
import org.antlr.runtime.RecognitionException;
import org.antlr.runtime.Token;
import org.antlr.runtime.UnwantedTokenException;
import org.antlr.runtime.tree.CommonTree;

import static speedith.core.i18n.Translations.i18n;

/**
 * Indicates an exception which can be raised during reading a spider diagram
 * from a string (i.e.: during parsing, translating, and semantic checking).
 * @author Matej Urbas [matej.urbas@gmail.com]
 */
public class ReadingException extends Exception {

    // <editor-fold defaultstate="collapsed" desc="Fields">
    private int lineNumber = -1;
    private int charIndex = -2;
    private CommonTree node;
    private Token token;
    // </editor-fold>

    // <editor-fold defaultstate="collapsed" desc="Constructors">
    /**
     * Creates a new instance of <code>ReadingException</code> without detail message.
     */
    public ReadingException() {
    }

    /**
     * Constructs an instance of <code>ReadingException</code> with the specified detail message.
     * @param msg the detail message.
     */
    public ReadingException(String msg) {
        super(msg);
    }

    /**
     * Constructs an instance of <code>ReadingException</code> with the specified detail message.
     * @param msg the detail message.
     * @param cause the cause for this exception.
     */
    public ReadingException(String msg, Throwable cause) {
        super(msg, cause);
    }

    /**
     * Constructs an instance of <code>ReadingException</code> with the specified detail message.
     * @param msg the detail message.
     * @param cause the cause for this exception.
     */
    public ReadingException(String msg, ParseException cause) {
        super(msg + " (" + cause.getOrigin().getErrorMessage(cause.getCause(), cause.getOrigin().getTokenNames()) + ")", cause.getCause());
        if (cause.getCause() instanceof MissingTokenException) {
            MissingTokenException mte = (MissingTokenException) cause.getCause();
            this.token = mte.inserted instanceof Token ? ((Token) mte.inserted) : null;
        } else if (cause.getCause() instanceof UnwantedTokenException) {
            this.token = ((UnwantedTokenException) cause.getCause()).getUnexpectedToken();
        } else {
            this.token = cause.getCause().token;
        }
    }

    /**
     * Constructs an instance of <code>ReadingException</code> with the specified detail message.
     * @param msg the detail message.
     * @param lineNumber the number of the line at which the reading hit an
     * error (-1 indicates that the line position is unknown).
     * @param charIndex the character position (in the line) at which the
     * reading hit an error (-2 indicates that the character position is
     * unknown).
     */
    public ReadingException(String msg, int lineNumber, int charIndex) {
        super(msg);
        this.lineNumber = lineNumber;
        this.charIndex = charIndex;
    }

    /**
     * Constructs an instance of <code>ReadingException</code> with the specified detail message.
     * @param msg the detail message.
     * @param node the AST node where the exception occurred.
     */
    public ReadingException(String msg, CommonTree node) {
        super(msg);
        this.node = node;
    }
    // </editor-fold>

    // <editor-fold defaultstate="collapsed" desc="Properties">
    /**
     * Returns the character position (in the line) at which the reading hit an
     * error.
     * <p>Note: -2 is returned if the character position is not
     * known.</p>
     * @return the character position (in the line) at which the reading hit an
     * error.
     * <p>Note: -2 is returned if the character position is not
     * known.</p>
     */
    public int getCharIndex() {
        if (charIndex < -1) {
            if (getToken() != null) {
                charIndex = getToken().getCharPositionInLine();
            } else if (getNode() != null) {
                charIndex = getNode().getCharPositionInLine();
            } else if (getCause() instanceof RecognitionException) {
                charIndex = ((RecognitionException) getCause()).charPositionInLine;
            }
        }
        return charIndex;
    }

    /**
     * Returns the number of the line at which the reading hit an error.
     * <p>Note: -1 is returned if the line number is not
     * known.</p>
     * @return the number of the line at which the reading hit an error.
     * <p>Note: -1 is returned if the line number is not
     * known.</p>
     */
    public int getLineNumber() {
        if (lineNumber < 0) {
            if (getToken() != null) {
                lineNumber = getToken().getLine();
            } else if (getNode() != null) {
                lineNumber = getNode().getLine();
            } else if (getCause() instanceof RecognitionException) {
                lineNumber = ((RecognitionException) getCause()).line;
            }
        }
        return lineNumber;
    }

    /**
     * Returns the AST node where the exception occurred.
     * @return the AST node where the exception occurred.
     */
    public CommonTree getNode() {
        return node;
    }

    /**
     * Sets the AST node where the exception occurred.
     * @param node the AST node where the exception occurred.
     */
    public void setNode(CommonTree node) {
        this.node = node;
    }

    /**
     * Returns the token which is somehow involved in the syntax error that
     * caused this exception.
     * @return the token which is somehow involved in the syntax error that
     * caused this exception.
     */
    public Token getToken() {
        return token;
    }

    /**
     * Sets the token which is somehow involved in the syntax error that
     * caused this exception.
     * @param token the token which is somehow involved in the syntax error that
     * caused this exception.
     */
    public void getToken(Token token) {
        this.token = token;
    }
    // </editor-fold>

    // <editor-fold defaultstate="collapsed" desc="Message Format Methods">
    @Override
    public String getLocalizedMessage() {
        if (getLineNumber() > 0 && getCharIndex() >= 0) {
            return i18n("ERR_TRANSLATION_EXCEPTION_MSG", getMessage(), getLineNumber(), getCharIndex());
        } else {
            return i18n("ERR_TRANSLATION_EXCEPTION_MSG_NO_POSITION", getMessage());
        }
    }
    // </editor-fold>
}
