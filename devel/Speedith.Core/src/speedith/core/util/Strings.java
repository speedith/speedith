/*
 *   Project: Speedith.Core
 *
 * File name: Sets.java
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
package speedith.core.util;

/**
 * Provides some utility and convenience functions for strings.
 * @author Matej Urbas [matej.urbas@gmail.com]
 */
public final class Strings {

    // <editor-fold defaultstate="collapsed" desc="Emptiness">
    /**
     * This is a convenience method that returns {@code true} if and only if the
     * given string is {@code null} or {@link String#isEmpty() empty}.
     * @param str the string we want to check.
     * @return {@code true} if and only if the
     * given string is {@code null} or {@link String#isEmpty() empty}.
     */
    public static boolean isNullOrEmpty(String str) {
        return str == null || str.isEmpty();
    }
    // </editor-fold>

    // <editor-fold defaultstate="collapsed" desc="Disabled Constructor">
    private Strings() {
    }
    // </editor-fold>
}
