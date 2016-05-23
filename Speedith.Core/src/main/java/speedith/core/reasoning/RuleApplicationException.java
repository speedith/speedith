/*
 *   Project: Speedith.Core
 * 
 * File name: RuleApplicationException.java
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
package speedith.core.reasoning;

/**
 *
 * @author Matej Urbas [matej.urbas@gmail.com]
 */
public class RuleApplicationException extends Exception {
    private static final long serialVersionUID = 0x2d9444064275ba88L;

    /**
     * Creates a new instance of <code>RuleApplicationException</code> without detail message.
     */
    public RuleApplicationException() {
    }

    /**
     * Constructs an instance of <code>RuleApplicationException</code> with the specified detail message.
     * @param msg the detail message.
     */
    public RuleApplicationException(String msg) {
        super(msg);
    }

    /**
     * Constructs an instance of <code>RuleApplicationException</code> with the specified detail message and initial
     * cause of the exception.
     * @param msg the detail message.
     * @param cause  the initial cause
     */
    public RuleApplicationException(String msg, Throwable cause) {
        super(msg, cause);
    }

    /**
     * Constructs an instance of <code>RuleApplicationException</code> with the specified initial
     * cause.
     * @param cause the initial cause
     */
    public RuleApplicationException(Throwable cause) {
        super(cause);
    }
}
