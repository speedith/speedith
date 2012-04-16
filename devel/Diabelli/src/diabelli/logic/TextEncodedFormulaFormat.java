/*
 * File name: TextEncodedFormulaFormat.java
 *    Author: Matej Urbas [matej.urbas@gmail.com]
 * 
 *  Copyright © 2012 Matej Urbas
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
package diabelli.logic;

/**
 * Formula formats of this type may be represented by a Unicode string. This
 * interface provides methods that perform the conversion.
 * @author Matej Urbas [matej.urbas@gmail.com]
 */
public interface TextEncodedFormulaFormat extends FormulaFormat {
    /**
     * Encodes the given formula into a Unicode string.
     * @param formula the formula to be encoded as a string.
     * @return the Unicode string that encodes the given formula.
     * @throws diabelli.logic.TextEncodedFormulaFormat.FormulaEncodingException
     * thrown if the encoding failed for any reason (for example, if the given
     * formula is not of this format).
     *  <p>The message in this exception will be shown to the user in the GUI,
     * it is therefore desired that the message be localised and human-readable.</p>
     */
    String encodeAsString(Formula formula) throws FormulaEncodingException;
    /**
     * Decodes a formula from the given string.
     * @param encodedFormula the string that contains the formula
     * @return the decoded formula.
     * @throws diabelli.logic.TextEncodedFormulaFormat.FormulaEncodingException
     * thrown if the decoding failed for any reason.
     *  <p>The message in this exception will be shown to the user in the GUI,
     * it is therefore desired that the message be localised and human-readable.</p>
     */
    Formula decodeFromString(String encodedFormula) throws FormulaEncodingException;

    //<editor-fold defaultstate="collapsed" desc="Exception Class">
    /**
     * This exception is thrown if the text encoding or decoding of a formula
     * failed. The message in this exception will be shown to the user in the GUI,
     * it is therefore desired that the message be localised and human-readable.
     */
    public static class FormulaEncodingException extends Exception {
        
        public FormulaEncodingException() {
        }
        
        public FormulaEncodingException(Throwable cause) {
            super(cause);
        }
        
        public FormulaEncodingException(String message, Throwable cause) {
            super(message, cause);
        }
        
        public FormulaEncodingException(String message) {
            super(message);
        }
    }
    //</editor-fold>
}
